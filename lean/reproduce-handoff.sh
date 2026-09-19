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
if test -f handoff-checkpoint-logs.tar.gz; then
  nice -n 10 taskset -c 0-31 tar -xzf handoff-checkpoint-logs.tar.gz
fi
nice -n 10 taskset -c 0-31 lake build > logs/handoff-build.txt 2>&1
nice -n 10 taskset -c 0-31 python3 MakeAudit.py > logs/handoff-audit-generation.txt
nice -n 10 taskset -c 0-31 lake env lean AuditAll.lean > AuditAll.txt 2>&1
nice -n 10 taskset -c 0-31 python3 VerifyAudit.py > Verification.json
nice -n 10 taskset -c 0-31 python3 check-part2.py > Part2Coverage.json
nice -n 10 taskset -c 0-31 python3 check-goal-round7.py > GoalRound7Preservation.json
nice -n 10 taskset -c 0-31 python3 check-handoff.py > HandoffPreservation.json
nice -n 10 taskset -c 0-31 lake env lean --version > Toolchain.txt
git -C .lake/packages/mathlib rev-parse HEAD >> Toolchain.txt
git rev-parse HEAD > Commit.txt
cat Verification.json
cat Part2Coverage.json
cat GoalRound7Preservation.json
cat HandoffPreservation.json
