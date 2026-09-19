# Reproducing the Lean build and axiom audit

Everything below runs from this directory on a fresh Linux or macOS machine.
Recorded reference run: Lean 4.24.0, Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`,
`lake build` 8093 jobs, `#print axioms` audit over 1585 declarations
(`Verification.json`, `AuditAll.txt`, `logs/handoff-build.txt`).

Requirements: `git`, `python3`, `xz`, about 10 GB of disk for the Mathlib
cache, and enough memory for one `lean` worker per thread (1-4 GB each; set
`LEAN_NUM_THREADS` if the machine is small).

## 1. Toolchain

Install [elan](https://github.com/leanprover/elan) if it is not present, then
let it install the pinned toolchain named in `lean-toolchain`:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan toolchain install "$(cat lean-toolchain)"    # leanprover/lean4:v4.24.0
lean --version                                     # Lean (version 4.24.0, ..., commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release); cf. Toolchain.txt
```

## 2. Dependencies and the Mathlib cache

`lake-manifest.json` pins Mathlib to commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
(tag `v4.24.0`) together with its transitive dependencies. Do not run
`lake update`; it would move the pins.

```sh
lake exe cache get      # clones the pinned packages into .lake/packages and downloads Mathlib's .olean cache
```

## 3. Build

```sh
lake build              # default target: the ProvenHashes library (741 modules under ProvenHashes/)
```

The recorded log ends with `Build completed successfully (8093 jobs).`
(`logs/handoff-build.txt`). With the Mathlib cache present, only the 741 local
modules and the root are compiled; the remaining jobs are cache checks.

## 4. Axiom audit

```sh
python3 MakeAudit.py                          # regenerates AuditAll.lean: `#check` and `#print axioms` for every local theorem/lemma
lake env lean AuditAll.lean > AuditAll.txt    # recorded: 1585 declarations, 0 errors
python3 VerifyAudit.py > Verification.json    # exits non-zero unless every report lists only propext, Classical.choice, Quot.sound
```

`VerifyAudit.py` also scans every `ProvenHashes/*.lean` for `sorry`, `admit`,
`native_decide`, `unsafe` and `axiom` declarations, and rewrites
`SourceHashes.json` with SHA-256 digests of the sources it audited.

To check a single headline theorem interactively:

```sh
cat > /tmp/audit_published128.lean <<'EOF'
import ProvenHashes
#check ProvenHashes.UMASH.published128
#print axioms ProvenHashes.UMASH.published128
EOF
lake env lean /tmp/audit_published128.lean
```

Expected output:

```
ProvenHashes.UMASH.published128 : ProvenHashes.UMASH.Published128
'ProvenHashes.UMASH.published128' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 5. Checking that the sources are the ones from commit 115d1ee

`SourceHashes.json` is the lane's manifest written by `VerifyAudit.py` at the
audited commit. Every `.lean` entry in it (744 files: `ProvenHashes/*.lean`,
`ProvenHashes.lean`, `AuditAll.lean`, `CheckModel.lean`) matches this
directory byte-for-byte:

```sh
python3 - <<'EOF'
import hashlib, json
from pathlib import Path
manifest = json.load(open('SourceHashes.json'))
lean = {p: h for p, h in manifest.items() if p.endswith('.lean')}
bad = [p for p, h in lean.items()
       if hashlib.sha256(Path(p).read_bytes()).hexdigest() != h]
print(len(lean), 'lean files in manifest;', len(bad), 'differ', bad)
EOF
```

The non-Lean entries that differ do so only because private paths and the
build host name were replaced by `<xeon>` placeholders (the eight `*.sh`
scripts and five review notes under `sources/`); two exploration scripts
listed in the manifest were not published. See `STATUS.md` for the list.

## 6. Optional: per-lemma checkpoint records

The lane compiled every new declaration in its own `lake build` checkpoint.
The records are:

- `Part2Checkpoints.json.xz` (`xz -dk Part2Checkpoints.json.xz` to expand;
  48 MiB of JSON, SHA-256 of the expanded file
  `3ed9bef8bedcefd32777c3ab2378b86d6cbf1d3bdafca06fac560c1ffe3b6f41`):
  one entry per checkpoint with the log path, the log's SHA-256 and the
  SHA-256 of every source module at that moment.
- `handoff-checkpoint-logs.tar.gz`: the 1143 build logs referenced by the
  manifest (`tar -xzf handoff-checkpoint-logs.tar.gz` restores them under
  `logs/`; `CheckpointArchive.json` records the archive's SHA-256
  `011aca4c46778619e0308f9f8168fdfb1ae2fb590fc900b887f56893852c376e`).
- `part2-build-logs.tar.gz`: the earlier 385 logs of the round-2 lane.

`check-handoff.py` runs from this directory once the ledger is expanded.
`check-part2.py` and `check-goal-round*.py` compare against earlier lane
commits with `git show` and therefore need the lane's own git history; their
recorded outputs are `Part2Coverage.json`, `HandoffPreservation.json` and
`GoalRound*Preservation.json`.

## 7. The lane's own scripts

`reproduce-handoff.sh`, `build-handoff.sh` and the older `reproduce*.sh` /
`build*.sh` are the scripts the lane ran on its build host. They assume Linux,
a pre-populated `.lake`, and pin CPU affinity with `taskset`; the hand-run
commands above are the portable equivalent. `CheckModel.lean` with
`check_model.py` is a smoke comparison of the Lean model against
`sources/umash_reference.py` at boundary lengths; it is not part of the proof.
