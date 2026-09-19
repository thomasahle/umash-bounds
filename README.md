# UMASH collision bounds: proofs and certificates

Proofs, exact numerical certificates and Lean sources for the collision bounds of
[UMASH](https://github.com/backtrace-labs/umash) discussed in
[backtrace-labs/umash#40](https://github.com/backtrace-labs/umash/issues/40).

| Document | Result |
| --- | --- |
| `proofs/PROOF1_corrected_envelope.md` | unconditional UMASH-64 envelope with block constant 364816 (45635·⌈L/512⌉/2^61, 46.52 bits); the ENH-only joint case |
| `proofs/PROOF2_ph_enh_joint_case.md` | the PH+ENH joint case (< 2^-90) and a sharp primary tag-only bound |
| `proofs/PROOF3_primary_constant_3125.md` | primary block constant 3125 (423·⌈L/512⌉/2^61, 53.38 bits) |
| `proofs/PROOF4_umash64_headline.md` | the published UMASH-64 headline holds: 58·⌈L/512⌉/2^61 (56.18 bits), via the implemented accumulator modulo 2^64−8 |
| `proofs/PROOF5_fingerprint_headline.md` | the published UMASH-128 fingerprint headline holds for the C architecture: (81/128)·⌈L/2^23⌉²·2^-83; the single-multiplier Python reference variant is refuted |

Scope: ideal full keys (34 OH words sampled without replacement, IID also covered), a fixed seed, independent uniform polynomial
multipliers, full outputs of the C architecture. The Salsa20 key derivation and per-call seeds are outside these theorems.

`checks/proofN/` holds the exact integer and rational certificates for each proof, with `README.md` and run scripts (written for a
96-thread Xeon; adjust the core pins). `lean/` mirrors the Lean 4 / Mathlib project that machine-checks PROOF1's envelope and the
ENH-only closure (`ProvenHashes.UMASH.certified_all_pairs64`, `open_enh_only_sharp`; audit in `AuditAll.txt`); the later proofs are
paper proofs with certificates and independent review, and their formalization is in progress.

Consolidated write-up: [`paper/umash_bounds.pdf`](paper/umash_bounds.pdf) (LaTeX source alongside), "Collision bounds for UMASH: closing the projection gap", 20 pages.
