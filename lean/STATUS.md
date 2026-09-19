# Machine-checked status of the UMASH bounds (2026-09-19)

This directory is the ProvenHashes Lean 4 project at the proof lane's final
audit commit. All declarations named below live in namespace
`ProvenHashes.UMASH`; probabilities are exact finite uniform counts in `ℚ≥0`
(`ProvenHashes.uniformProb`, `Probability.lean`).

## Provenance

| Item | Value |
| --- | --- |
| Fingerprint proof commit | `5baffb5286ccd406a110fcafa87c16ddec877431` (2026-09-19 15:42:20 +0000, "Prove the published two-multiplier fingerprint bound") |
| Snapshot / final audit commit (`git rev-parse 115d1ee`) | `115d1ee18b680645aeaed1885d77033fa6d1558d` (2026-09-19 15:56:31 +0000, "Reduce the primary headline to two block estimates") |
| Lane reporting commit (documentation only) | `863bcda7d87607f60b88d9b4b8819385668c661c` (2026-09-19 15:57:30 +0000); source of `LANE_REPORT.md`, `COMPARISON.md`, `HANDOFF_ROUND2_NOTES.md` |
| SHA-256 of `git archive --format=tar 115d1ee` (1030 files) | `2f5606e390c87158cccec8de46e46cd53e79254f515e699457d8c56977aea720` |
| Lean | 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b` (`Toolchain.txt`, `lean-toolchain`) |
| Mathlib | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (tag `v4.24.0`, pinned in `lake-manifest.json`) |
| Root `lake build` | 8093 jobs, `Build completed successfully` (`logs/handoff-build.txt`) |
| Axiom audit | 1585 theorems and lemmas (`AuditAll.lean`, `AuditAll.txt`); every report lists a subset of `propext`, `Classical.choice`, `Quot.sound` (1568 reports with axioms, 17 without); `Verification.json` = PASS |
| Source scan | no `sorry`, `admit`, `native_decide`, `unsafe`, or `axiom` declaration in `ProvenHashes/*.lean` (`VerifyAudit.py`) |
| Sources | 741 modules, 71,706 lines under `ProvenHashes/`; all 744 `.lean` entries of `SourceHashes.json` match byte-for-byte (see `REPRODUCE.md` §5) |

## The model

`ProvenHashes/UMASHModel.lean` defines the literal reference construction:
`q = 2^64`, `p = 2^61 − 1`, `Word = BitVec 64`, `Message = List (Fin 256)`,
34 OH words `OHKey = Fin 34 → Word`, the short-input mixer (`shortHash`, at
most 8 bytes), the overlapping 16-byte chunking (`chunkAt`, `encode`), PH and
ENH with the high-XOR-low fold (`ph`, `enh`), the byte-length block tag
(`blockTag`), both compressors (`oh`, `ohSecondary`), the accumulator modulo
`8p = 2^64 − 8` (`polyStep`, `polyReduce`) and the finalizer. The key spaces
of the headline theorems are

```lean
abbrev PolyKey := {f : Fin p // 1 < f.val}                 -- multiplier uniform on {2, …, p−1}
abbrev DistinctOHKey := {k : OHKey // Function.Injective k}  -- 34 pairwise-distinct words, uniform
abbrev Key64 := DistinctOHKey × PolyKey
abbrev Key128 := DistinctOHKey × (PolyKey × PolyKey)         -- shared OH words, two independent multipliers

def hash64 (k : Key64) (seed : Word) (m : Message) : Word :=
  hashWith k.1.val k.2.val.val seed m
def hash128 (k : Key128) (seed : Word) (m : Message) : Word × Word :=
  (hashWith k.1.val k.2.1.val.val seed m,
   hashWith k.1.val k.2.2.val.val seed m true)
```

Block-level propositions quantify over `Block` values (`chunks : List Chunk`
with the original byte count) satisfying `Block.Valid`, with the 34 OH words
IID uniform (`OHKey`); `primaryEvent seed x y k` is the collision of the
projected primary compressor outputs, `jointEvent` the simultaneous collision
of both compressors.

## Machine-checked headline theorems

Each entry gives the theorem, its module, the exact proposition it proves (as
defined in the source), and its line from `AuditAll.txt`.

### 1. UMASH-128 fingerprint headline: `published128`

Module `ProvenHashes/UMASHPublishedFingerprint.lean`; proposition in
`ProvenHashes/UMASHObligations.lean`.

```lean
def Published128 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
    (((L+2^23-1)/2^23 : ℕ) : ℚ≥0)^2 / (2:ℚ≥0)^83

theorem published128 : Published128
```

```
'ProvenHashes.UMASH.published128' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is the published fingerprint bound ⌈s/2^26⌉²·2^−83 for an s-byte cap
with s = 8L, for the C architecture (two independent multipliers, shared OH
words). The proof (`coarse_fingerprint_rate_le_published`) combines the
primary marginal 364816/q, the secondary marginal 729632/q and the joint block
bound below 2^−87 with the root counts of two independent multipliers, and
proves the rounding coefficient below 7/10, so the published coefficient 1
follows. PROOF5's sharper coefficient 81/128 is not claimed here (see "Paper
proofs" below).

### 2. UMASH-64 envelope, 46.52 bits: `certified_all_pairs64` and companions

Module `ProvenHashes/UMASHCertified.lean`; propositions in
`UMASHObligations.lean`, `UMASHCorrectedObligations.lean`,
`UMASHCorrectedAssembly.lean`; constants in `UMASHConstants.lean`.

```lean
def weakA : ℚ≥0 := (364816 : ℚ≥0) / (q-561 : ℕ)
def weakComplement : ℚ≥0 := ((q-561-364816 : ℕ) : ℚ≥0) / (q-561 : ℕ)
def rootRate (L : ℕ) : ℚ≥0 := min 1 (2 * (((L+31)/32 : ℕ) : ℚ≥0) / (p-2 : ℕ))
def certifiedEnvelope (L : ℕ) : ℚ≥0 :=
  if L = 1 then (1 : ℚ≥0) / (q-561 : ℕ) else weakA + weakComplement*rootRate L

def CertifiedAllPairs64 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤ certifiedEnvelope L

def CertifiedAllPairs64IID : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : OHKey × PolyKey =>
    hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y) ≤ certifiedEnvelope L

def CertifiedAllPairs128 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤ certifiedEnvelope L

def CorrectedLinear64 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
    45635 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61

def CorrectedLinear128 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
    45635 * (((L+511)/512 : ℕ) : ℚ≥0) / 2^61

theorem certified_all_pairs64     : CertifiedAllPairs64
theorem certified_all_pairs64_iid : CertifiedAllPairs64IID
theorem certified_all_pairs128    : CertifiedAllPairs128
theorem corrected_linear64        : CorrectedLinear64
theorem corrected_linear128       : CorrectedLinear128
```

```
'ProvenHashes.UMASH.certified_all_pairs64' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.certified_all_pairs64_iid' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.certified_all_pairs128' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.corrected_linear64' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.corrected_linear128' depends on axioms: [propext, Classical.choice, Quot.sound]
```

With `A = weakA = 364816/(q−561)` the envelope is ε(1) = 1/(q−561) and
ε(L ≥ 2) = A + (1−A)·min(1, 2⌈L/32⌉/(2^61−3)); its length-normalized score
is 46.52 bits (PROOF1). The underlying primary block bound
`corrected_primary_block_bound : CorrectedPrimaryBlockBound` (364816/q,
`UMASHCorrectedBlock.lean`) is closed as well.

### 3. ENH-only joint case: `joint_enh_only_bound`, `open_enh_only_sharp`

Module `ProvenHashes/UMASHJointClosure.lean`; propositions in
`UMASHCorrectedObligations.lean` and `UMASHObligations.lean`.

```lean
def JointENHOnlyBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → phDiffCount x y = 0 → lastChunk x ≠ lastChunk y →
  uniformProb (jointEvent seed x y) ≤ (4721784:ℚ≥0)/q^2

def OpenENHOnly : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → phDiffCount x y = 0 → enhChanges x y = 2 →
  32 ≤ enhValuation x y → enhValuation x y ≤ 63 →
  uniformProb (jointEvent seed x y) < (1:ℚ≥0)/2^87

theorem joint_enh_only_bound : JointENHOnlyBound
theorem open_enh_only_sharp  : OpenENHOnly
```

```
'ProvenHashes.UMASH.joint_enh_only_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.open_enh_only_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 4. PH+ENH joint case: `joint_phenh_sharp`, `open_phenh_sharp`

Modules `ProvenHashes/UMASHPHENHSharp.lean` and
`ProvenHashes/UMASHOpenPHENH.lean`; propositions in
`UMASHSharpObligations.lean` and `UMASHObligations.lean`.

```lean
def JointPHENHSharpBound : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → dataChecksum x = dataChecksum y →
  phDiffCount x y = 1 → enhChanges x y = 2 →
  1 ≤ enhValuation x y → enhValuation x y ≤ 63 →
  uniformProb (jointEvent seed x y) ≤ (170906186782 : ℚ≥0)/q^2

def OpenPHENH : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → dataChecksum x = dataChecksum y →
  phDiffCount x y = 1 → enhChanges x y = 2 →
  (enhValuation x y = 1 ∨ enhValuation x y = 2 ∨ enhValuation x y = 3 ∨
    (36 ≤ enhValuation x y ∧ enhValuation x y ≤ 63)) →
  uniformProb (jointEvent seed x y) < (1:ℚ≥0)/2^87

theorem joint_phenh_sharp : JointPHENHSharpBound
theorem joint_phenh_iid_lt90 (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hsum : dataChecksum x = dataChecksum y)
    (hp : phDiffCount x y = 1) (he : enhChanges x y = 2)
    (hr : 1 ≤ enhValuation x y) (hr' : enhValuation x y ≤ 63) :
    uniformProb (jointEvent seed x y) < (1:ℚ≥0)/2^90
theorem joint_phenh_distinct_lt90 (… same hypotheses …) :
    uniformProb (fun k : DistinctOHKey => jointEvent seed x y k.val) < (1:ℚ≥0)/2^90
theorem open_phenh_sharp : OpenPHENH
```

```
'ProvenHashes.UMASH.joint_phenh_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.joint_phenh_iid_lt90' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.joint_phenh_distinct_lt90' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.open_phenh_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 5. Sharp primary tag-only bound: `primary_tag_only_sharp`

Module `ProvenHashes/UMASHTagSharp.lean`; proposition in `UMASHSharpObligations.lean`.

```lean
def PrimaryTagOnlyBoundSharp : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → x.chunks = y.chunks → blockTag seed x ≠ blockTag seed y →
  uniformProb (primaryEvent seed x y) < (1 : ℚ≥0)/(8*q)

theorem primary_tag_only_sharp : PrimaryTagOnlyBoundSharp
```

```
'ProvenHashes.UMASH.primary_tag_only_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 6. Refutation of the shared-multiplier Python fingerprint: `reference_swap_*`

Modules `ProvenHashes/UMASHReferenceSwap.lean` and
`ProvenHashes/UMASHReferenceSwapProbability.lean`; propositions in
`UMASHContinuationObligations.lean`. `referenceFingerprint` runs both
compressors with one multiplier, as the Python API's key record does.

```lean
def referenceSwapX : Message := List.replicate 256 0 ++ List.replicate 256 1
def referenceSwapY : Message := List.replicate 256 1 ++ List.replicate 256 0

def ReferenceSwapCollision : Prop := ∀ (k : OHKey) (seed : Word),
  (hashWith k (p-1) seed referenceSwapX, hashWith k (p-1) seed referenceSwapX true) =
  (hashWith k (p-1) seed referenceSwapY, hashWith k (p-1) seed referenceSwapY true)

def ReferenceSwapLowerBound : Prop := ∀ (seed : Word),
  (1:ℚ≥0)/(p-2:ℕ) ≤ uniformProb (fun k : Key64 =>
    referenceFingerprint k seed referenceSwapX = referenceFingerprint k seed referenceSwapY)

theorem reference_swap_collision  : ReferenceSwapCollision
theorem reference_swap_lower_bound : ReferenceSwapLowerBound
```

```
'ProvenHashes.UMASH.reference_swap_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.reference_swap_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A collision probability of at least 1/(p−2) ≈ 2^−61 refutes an 83-bit claim
for that variant; the theorem says nothing against the C architecture, whose
fingerprint is item 1.

### Supporting block theorems used by item 1

All closed, all with the same three-axiom audit line:

| Theorem | Proposition | Module |
| --- | --- | --- |
| `secondary_block_bound` | `SecondaryBlockBound729632`: projected secondary compressor collision ≤ 729632/q for valid blocks with different chunks or tags | `UMASHSecondaryBlock.lean` |
| `joint_block_bound` | `JointBlockBound1416246956032`: `jointEvent` ≤ 1416246956032/q² for valid blocks with different chunks or tags | `UMASHJointBlockComplete.lean` |
| `subcase_b_bound` | `SubcaseBBound`: equal checksums, at least two PH changes, `jointEvent` ≤ 345763417/2^116 | `UMASHTwoPHBound.lean` |
| `ph_one_word_enh_bound` | `PHOneWordENHBound`: one PH change and one ENH word change, `jointEvent` < 2^−91 | `UMASHJointBlockComplete.lean` |
| `primary_enh_only_bound3125` | `PrimaryENHOnlyBound3125`: same count, no PH change, different last chunk, `primaryEvent` ≤ 3125/q | `UMASHENH3125.lean` |
| `quadratic_interval_count` | `QuadraticIntervalCount`: PROOF2 Lemma 4.1 for every finite set of integer preimages | `UMASHQuadraticIntervals.lean` |

## Conditional theorems (closed reductions with open premises)

These are theorems whose statements carry an explicitly open premise. They
are audited like every other declaration; they do not make the premise true.

### UMASH-64 headline, published coefficient 64

Modules `ProvenHashes/UMASHPrimaryHandoffAssembly.lean` (theorem) and
`ProvenHashes/UMASHPrimaryHandoffObligations.lean` (premises).

```lean
def Published64 : Prop := ∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
    ((L+511)/512 : ℕ) / (2:ℚ≥0)^55

def PrimaryFullBlockBound256 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → x.byteSize = 256 → y.byteSize = 256 → x.chunks ≠ y.chunks →
  uniformProb (primaryEvent seed x y) ≤ (256:ℚ≥0)/q

def PrimaryLastUpdateBound503 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (fun k : OHKey × PolyKey =>
    polyStep k.2.val.val 0 (oh k.1 x seed) =
      polyStep k.2.val.val 0 (oh k.1 y seed)) < (503:ℚ≥0)/q

def PrimaryHandoffAssembly : Prop :=
  PrimaryFullBlockBound256 → PrimaryLastUpdateBound503 → Published64

theorem published64_of_primary_handoff : PrimaryHandoffAssembly
```

```
'ProvenHashes.UMASH.published64_of_primary_handoff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The message classifier, root counting, OH conditioning and ceiling arithmetic
are closed; two branches are already unconditional
(`primary_other_counts_published`, `primary_short_long_published`, same
module). What remains is the two block estimates.

### Primary block constant 3125 (PROOF3)

Module `ProvenHashes/UMASHSharpOnePremise.lean`; propositions in
`UMASHSharpObligations.lean`, constants in `UMASHConstants.lean`.

```lean
def PrimaryPHBound1123 : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → 0 < phDiffCount x y →
  uniformProb (primaryEvent seed x y) ≤ (1123 : ℚ≥0)/q

def sharpA : ℚ≥0 := (3125 : ℚ≥0) / (q-561 : ℕ)
def certifiedEnvelope3125 (L : ℕ) : ℚ≥0 :=
  if L = 1 then (1 : ℚ≥0) / (q-561 : ℕ) else sharpA + sharpComplement*rootRate L

theorem certified64_3125_of_ph  (hph : PrimaryPHBound1123) : CertifiedAllPairs64_3125
theorem certified128_3125_of_ph (hph : PrimaryPHBound1123) : CertifiedAllPairs128_3125
```

```
'ProvenHashes.UMASH.certified64_3125_of_ph' depends on axioms: [propext, Classical.choice, Quot.sound]
'ProvenHashes.UMASH.certified128_3125_of_ph' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open propositions (definitions only)

No theorem in this snapshot proves any of the following; they are definitions
of propositions in `UMASHObligations.lean`, `UMASHSharpObligations.lean`,
`UMASHContinuationObligations.lean` and
`UMASHPrimaryHandoffObligations.lean`, never assumed as axioms.

| Proposition | Content | Paper status |
| --- | --- | --- |
| `Published64` | published coefficient 64: ⌈L/512⌉/2^55 | PROOF4 (proves the stronger 58) |
| `Published64Strong`, `Published64StrongIID`, `Published64Envelope` | 58·⌈L/512⌉/2^61 (distinct / IID keys) and PROOF4's finer envelope (56.18 bits) | PROOF4 |
| `PrimaryFullBlockBound256`, `PrimaryLastUpdateBound503` | the two block estimates that would close `Published64` | see `LANE_REPORT.md` |
| `PrimaryPHBound1123` | PH-changing primary block ≤ 1123/q | PROOF3 Lemma 3.1(d),(e) and assembly |
| `PrimaryBlockBound3125`, `IIDLongPrimaryIdentityBound3125`, `LongPrimaryIdentityBound3125`, `CertifiedAllPairs64_3125`, `CertifiedAllPairs128_3125`, `CorrectedLinear64_423`, `CorrectedLinear128_423` | the 3125 family (423·⌈L/512⌉/2^61, 53.38 bits) | PROOF3; closed in Lean from `PrimaryPHBound1123` |
| `Published128Strong`, `Published128StrongIID`, `Published128StrongNonzero`, `Published128StrongIIDNonzero`, `Published128Inherited58` | (81/128)·⌈L/2^23⌉²·2^−83 under the four samplers, and the 58-coefficient inheritance | PROOF5 |
| `SharpPrimaryProjection` | the disputed intermediate estimate 162/(q−561) | not claimed anywhere |

## What this means for the published UMASH claims

| Published claim | Machine-checked | Paper proof in this repository |
| --- | --- | --- |
| Fingerprint: ⌈s/2^26⌉²·2^−83 (C architecture, two multipliers) | yes, `published128` (coefficient 1) | PROOF5 sharpens to 81/128 |
| Fingerprint for the Python reference (one multiplier) | refuted, `reference_swap_lower_bound` | PROOF5 §11 |
| UMASH-64: ⌈s/4096⌉·2^−55 (coefficient 64) | reduced to two open block estimates | PROOF4 proves 58·⌈L/512⌉/2^61 (56.18 bits) |
| UMASH-64 envelope 46.52 bits and linear 45635·⌈L/512⌉/2^61 | yes | PROOF1 |
| Primary block constant 3125 (53.38 bits) | conditional on `PrimaryPHBound1123` | PROOF3 |
| Joint cases ENH-only and PH+ENH below 2^−87 (and 2^−90) | yes | PROOF1, PROOF2 |
| Sharp primary tag-only < 1/(8q) | yes | PROOF2 |

Scope of every theorem: ideal full keys as in `Key64`/`Key128` (or IID OH
words where stated), a fixed seed, and the literal reference construction.
The Salsa20 key expansion and per-call seeding are outside the model.

## Contents of this snapshot and deviations from the archive

Source: `git archive --format=tar 115d1ee` of the proof lane (1030 files,
SHA-256 above). Published here:

- unchanged: all 741 `ProvenHashes/*.lean`, `ProvenHashes.lean`,
  `AuditAll.lean`, `CheckModel.lean`, `lakefile.toml`, `lake-manifest.json`,
  `lean-toolchain`, `AuditAll.txt`, `Verification.json`, `SourceHashes.json`,
  `Toolchain.txt`, `Commit.txt`, `ProofSourceCommit.txt`, the checkpoint,
  coverage and preservation `*.json` records, `CheckpointArchive.json`,
  `logs/` (7 files), `handoff-checkpoint-logs.tar.gz`
  (SHA-256 `011aca4c46778619e0308f9f8168fdfb1ae2fb590fc900b887f56893852c376e`),
  `part2-build-logs.tar.gz`, the Python scripts, `sources/` and the lane's
  notes;
- replaced: the lane's `STATUS.md` (written before `published128` was
  proved and therefore stating that the endpoint was open) by this file, with
  the lane's updated report from commit `863bcda` as `LANE_REPORT.md`;
  `COMPARISON.md` and `HANDOFF_ROUND2_NOTES.md` also from `863bcda`
  (that commit changed only these documents and `Commit.txt`); `README.md`
  by an orientation page; `.gitignore` by a minimal one (the lane's ignored
  its own audit outputs);
- excluded: `staged/` (146 staging copies of `ProvenHashes` modules: 143
  byte-identical, 3 stale variants), the 16 root `*.stage.lean` staging
  files, and `explore-low-weights.py`, `explore-two-ph.py` (exploration
  scripts reading a file outside the repository). None of these is imported
  by the library or used by the audit;
- compressed: `Part2Checkpoints.json` (50,375,616 bytes) as
  `Part2Checkpoints.json.xz`; SHA-256 of the expanded file
  `3ed9bef8bedcefd32777c3ab2378b86d6cbf1d3bdafca06fac560c1ffe3b6f41`;
- placeholder scrub: in the eight `*.sh` scripts the `ELAN_HOME` line now
  defaults to `$HOME/.elan`; in `LANE_REPORT.md`, `LEAN_UMASH_STATUS.md`,
  `LEAN_UMASH_CORRECTED_STATUS.md`, `LEAN_UMASH_CORRECTED_2_STATUS.md`,
  `README_UMASH.md` and five review notes under `sources/`, the build host
  name and home-directory paths are written `<xeon>`. These are the only
  files whose `SourceHashes.json` entries differ.

`Commit.txt` (`a4ef141…`) and `ProofSourceCommit.txt` (`517811f…`) are the
lane's own records from earlier reproduction runs, not the snapshot commit.
The previous public copy of `lean/` (76 modules) also carried 33 progress
notes that the lane never committed (`*Checkpoints.txt`, `*Remaining.txt`,
`*Check.txt`, intermediate `ReproductionRound2-*.txt`); they are not in
commit `115d1ee` and were dropped, their content being superseded by the
JSON checkpoint ledgers and the final audit.
The lane's earlier ledgers (`LEAN_UMASH*_STATUS.md`, `GOAL_ROUND*_NOTES.md`,
`ROUND2_PROOFS.md`) describe the state at the time each was written.
