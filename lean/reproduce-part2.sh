#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS=8
test "$(uname -s)" = Linux
test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = f897ebcf72cd16f89ab4577d0c826cd14afaafc7
test "$(cat lean-toolchain)" = leanprover/lean4:v4.24.0
mkdir -p logs
if test -f part2-build-logs.tar.gz; then
  tar -xzf part2-build-logs.tar.gz
fi
if test "${1:-}" = --recheck-high-ledgers; then
  nice -n 10 taskset -c 56-63 python3 reproduce-high-ledgers.py 4 > RecheckHighLedgers.txt 2>&1
fi
nice -n 10 taskset -c 56-63 lake build > BuildUMASHCorrected2.txt 2>&1
nice -n 10 taskset -c 56-63 python3 MakeAudit.py > AuditGeneration.txt
nice -n 10 taskset -c 56-63 lake env lean AuditAll.lean > AuditAll.txt 2>&1
nice -n 10 taskset -c 56-63 python3 VerifyAudit.py > Verification.json
nice -n 10 taskset -c 56-63 python3 check-part2.py > Part2Coverage.json
nice -n 10 taskset -c 56-63 python3 check-goal-round2.py > GoalRound2Preservation.json
nice -n 10 taskset -c 56-63 python3 check-goal-round3.py > GoalRound3Preservation.json
nice -n 10 taskset -c 56-63 python3 check-goal-round4.py > GoalRound4Preservation.json
nice -n 10 taskset -c 56-63 python3 check-goal-round5.py > GoalRound5Preservation.json
nice -n 10 taskset -c 56-63 python3 check-goal-round6.py > GoalRound6Preservation.json
nice -n 10 taskset -c 56-63 python3 check-goal-round7.py > GoalRound7Preservation.json
nice -n 10 taskset -c 56-63 lake env lean --version > Toolchain.txt
git -C .lake/packages/mathlib rev-parse HEAD >> Toolchain.txt
git rev-parse HEAD > Commit.txt
cat Verification.json
cat Part2Coverage.json
cat GoalRound2Preservation.json
cat GoalRound3Preservation.json
cat GoalRound4Preservation.json
cat GoalRound5Preservation.json
cat GoalRound6Preservation.json
cat GoalRound7Preservation.json
