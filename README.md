# UMASH collision bounds: proofs, certificates and Lean formalization

Proofs, exact numerical certificates and a machine-checked Lean 4 development for the collision bounds of
[UMASH](https://github.com/backtrace-labs/umash) discussed in
[backtrace-labs/umash#40](https://github.com/backtrace-labs/umash/issues/40).

## Status as of 2026-09-19

Machine-checked means: a closed Lean theorem in `lean/` about the literal reference construction, audited with
`#print axioms` to depend only on `propext`, `Classical.choice` and `Quot.sound` (proof lane commit
`5baffb5286ccd406a110fcafa87c16ddec877431`, final audit commit `115d1ee18b680645aeaed1885d77033fa6d1558d`; Lean 4.24.0,
Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`). Paper proof means: a natural-language proof in `proofs/` with exact
certificates in `checks/` and independent review, not (yet) closed in Lean.

| Claim | Bound | Status |
| --- | --- | --- |
| UMASH-128 fingerprint headline (PROOF5) | ⌈L/2^23⌉² · 2^−83 | **Machine-checked**: `ProvenHashes.UMASH.published128` |
| UMASH-64 envelope, 46.52 bits (PROOF1) | 45635·⌈L/512⌉/2^61; finer envelope with A = 364816/(q−561) | **Machine-checked**: `certified_all_pairs64`, `certified_all_pairs64_iid`, `corrected_linear64`, and the 128-bit inheritance `certified_all_pairs128`, `corrected_linear128` |
| ENH-only joint case (PROOF1) | 4721784/q² (< 2^−87) | **Machine-checked**: `joint_enh_only_bound`, `open_enh_only_sharp` |
| PH+ENH joint case (PROOF2) | 170906186782/q² (< 2^−90) | **Machine-checked**: `joint_phenh_sharp`, `joint_phenh_iid_lt90`, `open_phenh_sharp` |
| Sharp primary tag-only bound (PROOF2) | < 1/(8q) | **Machine-checked**: `primary_tag_only_sharp` |
| Python reference fingerprint with a shared multiplier refuted (PROOF5 §11) | collision probability ≥ 1/(p−2) on an explicit block-swap pair | **Machine-checked**: `reference_swap_collision`, `reference_swap_lower_bound` |
| UMASH-64 headline 58·⌈L/512⌉/2^61, 56.18 bits (PROOF4) | 58·⌈L/512⌉/2^61 | Paper proof. In Lean the published coefficient 64 is reduced to two block estimates, `published64_of_primary_handoff : PrimaryFullBlockBound256 → PrimaryLastUpdateBound503 → Published64`; both premises are open |
| Primary block constant 3125, 53.38 bits (PROOF3) | 423·⌈L/512⌉/2^61 | Paper proof. The ENH-only 3125 layer is checked (`primary_enh_only_bound3125`); the all-pairs assembly is conditional on the PH premise, `certified64_3125_of_ph (hph : PrimaryPHBound1123)` |
| Fingerprint coefficient 81/128 (PROOF5) | (81/128)·⌈L/2^23⌉²·2^−83 | Paper proof; needs the 3125 primary marginal. Lean proves the published coefficient 1 unconditionally |

**The fingerprint theorem.** `published128` states that for every L ≥ 1, every 64-bit seed and all distinct byte
strings x ≠ y of at most 8L bytes,

    Pr_k [ hash128 k seed x = hash128 k seed y ] ≤ ⌈L/2^23⌉² / 2^83,

where the probability is an exact count over `Key128`: the 34 OH words drawn uniformly among pairwise-distinct
34-tuples of 64-bit words, and two polynomial multipliers drawn independently and uniformly from {2, …, p−1},
p = 2^61−1, independently of the OH words. This is the C architecture's fingerprint: both compressors share the OH
words and have their own multiplier. `hash128` is the literal reference construction, with the short-input mixer for
at most 8 bytes, the overlapping 16-byte chunking, the PH and ENH compressors including ENH's high-XOR-low fold, the
byte-length block tags, the accumulator modulo 8p = 2^64−8 (not modulo p) and the finalizer; every short/long and
equal/unequal block-count combination is covered. The proof assembles the checked compressor marginals 364816/q
(primary) and 729632/q (secondary) with the checked joint block bound below 2^−87 and proves the rounding
coefficient below 7/10, which gives the published coefficient 1; PROOF5's sharper 81/128 needs the 3125 marginal
and remains a paper result.

Scope of all theorems: ideal full keys (34 OH words sampled without replacement; IID also covered where stated), a
fixed seed, independent uniform polynomial multipliers, full outputs of the C architecture. The Salsa20 key derivation
and per-call seeds are outside these theorems.

## Documents

| Document | Result |
| --- | --- |
| `proofs/PROOF1_corrected_envelope.md` | unconditional UMASH-64 envelope with block constant 364816 (45635·⌈L/512⌉/2^61, 46.52 bits); the ENH-only joint case |
| `proofs/PROOF2_ph_enh_joint_case.md` | the PH+ENH joint case (< 2^-90) and a sharp primary tag-only bound |
| `proofs/PROOF3_primary_constant_3125.md` | primary block constant 3125 (423·⌈L/512⌉/2^61, 53.38 bits) |
| `proofs/PROOF4_umash64_headline.md` | the published UMASH-64 headline holds: 58·⌈L/512⌉/2^61 (56.18 bits), via the implemented accumulator modulo 2^64−8 |
| `proofs/PROOF5_fingerprint_headline.md` | the published UMASH-128 fingerprint headline holds for the C architecture: (81/128)·⌈L/2^23⌉²·2^-83; the single-multiplier Python reference variant is refuted |

`checks/proofN/` holds the exact integer and rational certificates for each proof, with `README.md` and run scripts (written for a
96-thread Xeon; adjust the core pins).

`lean/` is the complete ProvenHashes Lean project at commit `115d1ee` (741 modules, 71,706 lines): `lake build` with
8093 jobs, `#print axioms` over all 1585 theorems and lemmas, no `sorry`, `admit`, `native_decide` or `unsafe`.
[`lean/STATUS.md`](lean/STATUS.md) lists every headline theorem with its exact Lean statement, module and audit line,
and what remains open; [`lean/REPRODUCE.md`](lean/REPRODUCE.md) gives the build and audit commands.

Consolidated write-up: [`paper/umash_bounds.pdf`](paper/umash_bounds.pdf) (LaTeX source alongside), "Collision bounds
for UMASH: closing the projection gap", 20 pages. Its section "Scope and machine-checked status" was written before the
fingerprint theorem and the PH+ENH sharp bound were closed in Lean; the table above and `lean/STATUS.md` are current.
