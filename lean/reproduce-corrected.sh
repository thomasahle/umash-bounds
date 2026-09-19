#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export ELAN_HOME="$HOME/agents/lean-hash/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=8
test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
mkdir -p logs
nice -n 10 taskset -c 56-63 lake build > BuildUMASHCorrected.txt 2>&1
nice -n 10 taskset -c 56-63 python3 MakeAudit.py > AuditGeneration.txt
nice -n 10 taskset -c 56-63 lake env lean AuditAll.lean > AuditAll.txt 2>&1
nice -n 10 taskset -c 56-63 python3 VerifyAudit.py > Verification.json
nice -n 10 taskset -c 56-63 lake env lean --version > Toolchain.txt
git -C .lake/packages/mathlib rev-parse HEAD >> Toolchain.txt
git rev-parse HEAD > Commit.txt
cat Verification.json
