#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=16
test "$(uname -s)" = Linux
test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = f897ebcf72cd16f89ab4577d0c826cd14afaafc7
test "$(cat lean-toolchain)" = leanprover/lean4:v4.24.0
mkdir -p logs
log="logs/handoff-$1-$(date +%Y%m%dT%H%M%S%N).txt"
if nice -n 10 taskset -c 0-31 lake build "${@:2}" > "$log" 2>&1; then
  tail -4 "$log"
  nice -n 10 taskset -c 0-31 python3 - "$1" "$log" <<'PY'
from pathlib import Path
import fcntl, hashlib, json, sys
with open('.part2-checkpoints.lock', 'a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    path = Path('Part2Checkpoints.json')
    data = json.loads(path.read_text()) if path.exists() else []
    sources = {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted(Path('ProvenHashes').glob('*.lean'))}
    data.append({'checkpoint': sys.argv[1], 'log': sys.argv[2],
                 'log_sha256': hashlib.sha256(Path(sys.argv[2]).read_bytes()).hexdigest(),
                 'source_sha256': sources})
    path.write_text(json.dumps(data, indent=2) + '\n')
PY
else
  rg -n -A 22 '^error:' "$log"
  exit 1
fi
