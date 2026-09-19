# Lean development: `ProvenHashes.UMASH`

A complete, buildable snapshot of the Lean 4 / Mathlib project that
machine-checks the UMASH collision bounds in this repository, taken at proof
commit `115d1ee18b680645aeaed1885d77033fa6d1558d` of the proof lane
(2026-09-19). Start with:

- [`STATUS.md`](STATUS.md): every headline theorem with its exact Lean
  statement, module and `#print axioms` line; which published UMASH claims are
  machine-checked and which remain paper proofs.
- [`REPRODUCE.md`](REPRODUCE.md): toolchain, `lake exe cache get`,
  `lake build`, and the audit commands.
- [`LANE_REPORT.md`](LANE_REPORT.md): the proof lane's own round report
  (reporting commit `863bcda`), kept for provenance.

## Layout

| Path | Content |
| --- | --- |
| `ProvenHashes/` | 741 Lean modules (71,706 lines). `UMASHModel.lean` defines the literal hash; `UMASHObligations.lean`, `UMASHCorrectedObligations.lean`, `UMASHSharpObligations.lean`, `UMASHContinuationObligations.lean`, `UMASHPrimaryHandoffObligations.lean` define the named propositions (never assumed); the remaining modules prove them. `Classic*.lean`, `Probability.lean`, `Polynomial.lean` are the inherited finite-probability and polynomial core (with GHASH/Poly1305 examples). |
| `ProvenHashes.lean` | Library root: 101 imports that reach every module transitively. |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Build configuration; Mathlib pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, Lean `v4.24.0`. |
| `AuditAll.lean`, `AuditAll.txt`, `Verification.json`, `SourceHashes.json`, `Toolchain.txt` | The axiom audit as run at the snapshot commit: 1585 theorems and lemmas, only `propext`, `Classical.choice`, `Quot.sound`. |
| `MakeAudit.py`, `VerifyAudit.py` | Generate and check the audit. |
| `logs/` | The final root build log (`handoff-build.txt`) and the short reproduction records. |
| `Part2Checkpoints.json.xz`, `handoff-checkpoint-logs.tar.gz`, `part2-build-logs.tar.gz`, `*Checkpoints*.json`, `*Coverage.json`, `*Preservation.json`, `CheckpointArchive.json` | Per-lemma build checkpoints and the preservation checks of earlier baselines. |
| `CheckModel.lean`, `check_model.py`, `sources/umash_reference.py` | Smoke comparison of the Lean model with the reference Python implementation (not part of the proofs). |
| `sources/` | Reference material used by the lane: the UMASH reference code, the corrected proof and verdict notes, and the classic-hash sources. |
| `COMPARISON.md`, `DEFECTS.md`, `HANDOFF_ROUND_NOTES.md`, `HANDOFF_ROUND2_NOTES.md`, `GOAL_ROUND*_NOTES.md`, `ROUND2_PROOFS.md`, `LEAN_UMASH*_STATUS.md`, `README_UMASH.md` | The lane's working notes and earlier status ledgers, in chronological order. They are historical: statements such as "the two requested endpoints remain unproved" describe the state when each was written. `STATUS.md` is authoritative. |

## Headline theorems

| Theorem | Module |
| --- | --- |
| `published128 : Published128` | `ProvenHashes/UMASHPublishedFingerprint.lean` |
| `certified_all_pairs64`, `certified_all_pairs64_iid`, `certified_all_pairs128`, `corrected_linear64`, `corrected_linear128` | `ProvenHashes/UMASHCertified.lean` |
| `joint_enh_only_bound`, `open_enh_only_sharp` | `ProvenHashes/UMASHJointClosure.lean` |
| `joint_phenh_sharp`, `joint_phenh_iid_lt90`, `joint_phenh_distinct_lt90` | `ProvenHashes/UMASHPHENHSharp.lean` |
| `open_phenh_sharp` | `ProvenHashes/UMASHOpenPHENH.lean` |
| `reference_swap_collision`, `reference_swap_lower_bound` | `ProvenHashes/UMASHReferenceSwap.lean`, `UMASHReferenceSwapProbability.lean` |
| `published64_of_primary_handoff` (conditional) | `ProvenHashes/UMASHPrimaryHandoffAssembly.lean` |
| `certified64_3125_of_ph`, `certified128_3125_of_ph` (conditional) | `ProvenHashes/UMASHSharpOnePremise.lean` |

Placeholders: `<xeon>` in the notes and scripts stands for the lane's build
host and its workspace root.
