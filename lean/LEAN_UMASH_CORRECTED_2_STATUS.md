STATUS: PARTIAL

## DECISION (before builds, 2026-09-19)

Continue **in place** in `<xeon>/lean-umash-corrected-2`, using
ProvenHashes.UMASH, Lean 4.24.0 and the existing Mathlib cache. Do not provision
the handoff's Lean 4.19 project. The comparison is in [COMPARISON.md](COMPARISON.md).
Its uncompiled project leaves the same major analytic reductions open and
would duplicate accepted implementation, probability, and algebra work.

Preserve the uncommitted round-7 continuation as well as commit `41d6558`.
First validate that continuation, then extend the existing development.
All builds/checks use the Xeon, `nice -n 10 taskset -c 0-31`, and
`LEAN_NUM_THREADS=16`. The Mac is used for reading, edits, and transfers.

For Published128, use the handoff's observation that coarse marginals suffice;
retain the separate stronger PROOF3/PROOF5 obligations. The corresponding
rounding coefficient is now proved below 7/10. For Published64, the
full-block/last-update route remains to be formalized; saved cell inequalities
alone are not a soundness proof.

## Remaining obligations

The two requested endpoints remain unproved. These are the unchanged exact
propositions in namespace `ProvenHashes.UMASH`:

```lean
-- published64 : Published64
∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
    ((L+511)/512 : ℕ) / (2:ℚ≥0)^55

-- published128 : Published128
∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
    (((L+2^23-1)/2^23 : ℕ) : ℚ≥0)^2 / (2:ℚ≥0)^83
```

Published64 needs sharper PH/common-PH block estimates, the complete
last-update count with the literal modulus, and the message decision list.
Published128 needs the two joint rows below and the long/long and short/long
two-mode polynomial-identity reductions. The full secondary block marginal,
short/short fingerprint collision count, and OH averaging of two independent
root bounds are now proved. These are substantial prerequisites, not either
requested endpoint.

The exact remaining joint-block rows are:

```lean
-- SubcaseBBound
∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → dataChecksum x = dataChecksum y →
  2 ≤ phDiffCount x y →
  uniformProb (jointEvent seed x y) ≤ (345763417:ℚ≥0)/2^116

-- PHOneWordENHBound
∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → dataChecksum x = dataChecksum y →
  phDiffCount x y = 1 → enhChanges x y = 1 →
  uniformProb (jointEvent seed x y) < (1:ℚ≥0)/2^91

-- JointBlockBound1416246956032
∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (jointEvent seed x y) ≤ (1416246956032:ℚ≥0)/q^2
```

The first needs two actual PH slices, the shuffler-difference rank bound,
compatibility-mask counts and the conditional long-mask twisting estimate.
The existing `rank_lemma64` is only one ingredient. The second can use the
handoff's one-word high-XOR atom `(2v+1)/q`, whose dyadic-bin counting proof
has not yet been formalized. The third now has an exhaustive assembly with
exactly the first two as premises:

```lean
joint_block_bound_of_two_rows :
  SubcaseBBound → PHOneWordENHBound → JointBlockBound1416246956032
```

The remaining 3125 prerequisite is unchanged:

```lean
-- PrimaryPHBound1123
∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → 0 < phDiffCount x y →
  uniformProb (primaryEvent seed x y) ≤ (1123:ℚ≥0)/q
```

PROOF3 Lemma 3.1(a)–(c), truncation, F_r/ENH 3125, and sharp primary
tag-only are proved. Parts (d),(e), convolution identity (7), and the PH
valuation/block-key assembly remain. Their precise counting obligations are:

```lean
∀ (n δ ε e : ℕ), 4 ≤ n → δ%4 = 2 → 2 ∣ ε →
  0 < e → e < 2^n → padicValNat 2 e = 2 →
  uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
    lowENHXor n δ ε ab.1.val ab.2.val = e) ≤ (5:ℚ≥0)/2^n

∀ (n δ ε : ℕ), 4 ≤ n → 2 ∣ δ → 2 ∣ ε →
  uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
    lowENHXor n δ ε ab.1.val ab.2.val = 2^n-8) ≤ ((n+12:ℕ):ℚ≥0)/2^n
```

The corresponding width-uniform `BitVec n` interfaces are also required:
replace each operand space by `BitVec n × BitVec n`, each `.val` by `.toNat`,
and introduce the same `Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv`
instance used by `lowENHXor_minimal_probability_bitvec`. No finite-width
certificate is substituted for these universal statements.

The following remaining propositions are exact, unchanged definitions in
[UMASHSharpObligations.lean](lean/ProvenHashes/UMASHSharpObligations.lean):

```lean
PrimaryBlockBound3125
IIDLongPrimaryIdentityBound3125
LongPrimaryIdentityBound3125
CertifiedAllPairs64_3125
CertifiedAllPairs128_3125
CorrectedLinear64_423
CorrectedLinear128_423
```

They all have checked assemblies from `PrimaryPHBound1123`; that premise
is not discharged. In particular, the requested 3125 all-pairs targets are:

```lean
∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤ certifiedEnvelope3125 L

∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤ certifiedEnvelope3125 L
```

The stronger endpoint and sampler propositions below also remain, with their
precise definitions preserved in
[UMASHContinuationObligations.lean](lean/ProvenHashes/UMASHContinuationObligations.lean):

```lean
Published64Envelope
Published64Strong
Published64StrongIID
Published128Inherited58
Published128Strong
Published128StrongIID
Published128StrongNonzero
Published128StrongIIDNonzero
```

These require the same missing analytic/message layers and their specified
sampler transfers. PROOF5's stronger 81/128 result additionally needs the
3125 primary marginal; the original Published128 target can use the proved
coarser marginal. No extra-premise theorem is called `published64` or
`published128`.

## Corrections

No requested bound was found false, and no requested proposition was changed.
[DEFECTS.md](DEFECTS.md) records a historical note's incorrect assertion of
exact polynomial degree; the consolidated paper already uses the correct
upper bound, so this does not affect either headline.

The arrival build exposed a delivery problem in the previous round: the root
imported `UMASHPHENHSharp.lean`, but only its staging file existed. This
continuation compiled all nine closure lemmas separately, repairing the
last maximum theorem's excessive definitional unfolding. The fifteen
certificate modules and all old theorem sources were retained.

## Milestones and signatures

The following are closed declarations, without an analytic premise:

```lean
joint_phenh_sharp : JointPHENHSharpBound
different_checksums_bound : DifferentChecksumsBound
secondary_block_bound : SecondaryBlockBound729632
joint_tag_only_bound : TagOnlyBound
closed_ph_two_word_enh_bound : ClosedPHTwoWordENHBound
one_word_enh_bound : OneWordENHBound
closed_two_word_enh_bound : ClosedTwoWordENHBound
```

`joint_phenh_iid_lt90` and `joint_phenh_distinct_lt90` give the strict
90-bit conclusions. `phenh_sixty_case_maximum` proves that shuffler 2 in
the high row attains the maximum over all sixty cases.

Other checked results:

- Different data checksums: joint probability at most `364816²/q²`.
- Different chunk counts: joint probability at most `29914913/q²`.
- Short/short fingerprints, including overlapping noise indices:
  `short_fingerprint_iid` gives `1/q²`; `short_fingerprint_distinct` gives
  `1/(q*(q-561))` on the literal `Key128` experiment.
- `averaged_independent_polynomial_roots` averages the product of root bounds
  over arbitrary finite OH data, retaining both marginal identity events
  and their joint event.
- `fingerprint_coarse_rounding_certificate` proves the coarse-marginal
  rounding coefficient is below `7/10 < 1`. This is arithmetic, not a
  message-level collision theorem.
- `joint_block_bound_of_two_rows` is explicitly conditional; all other
  joint block branches are now assembled. The two premises are listed above.

Every previously accepted primary, ENH-only, IID, linear, inheritance,
mod-8p accumulator, shuffler, tag-only and reference-swap theorem is retained.

## Axioms, commits, and reproduction

Vehicle: `<xeon>/lean-umash-corrected-2` on the Xeon. Source mirror: `lean/`.
Baseline commit: `41d6558609f9406b0405171636097d0949749461`.
Toolchain: Lean 4.24.0. Mathlib:
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

The full `lake build` passes (8051 jobs). The complete `#print axioms`
audit passes for **1444 theorem/lemma declarations**, with only `propext`,
`Classical.choice`, and `Quot.sound`. The source scan finds no prohibited
declarations. The per-lemma coverage check passes: 454 parent declarations,
990 subsequent declarations, 1001 successful checkpoints, none missing.
All **203 baseline source modules** are byte-for-byte preserved, and all
baseline root imports remain. A separate arrival-snapshot check also
preserves all **687 modules present on arrival**, including uncommitted
round-7 work.

Proof/certificate commit:
`a4ef141046a57e14eb1caf3c24c508c06feb3d56`
(`Close UMASH sharp ledger and joint collision cases`). This includes the
completed inherited certificates, 37 new theorem declarations, the nine
sharp-ledger closure declarations, audit output, and the checkpoint archive.
The sources and evidence are mirrored in `lean/`.

Reproduction command on the cached Xeon workspace:

```bash
bash reproduce-handoff.sh
```

This checks the toolchain and cached Mathlib artifact before building,
uses `nice -n 10 taskset -c 0-31` and 16 Lean threads, audits every local
theorem, and checks all per-lemma logs and preservation of the baseline.
It neither installs the handoff's 4.19 project nor rebuilds Mathlib.

Evidence paths, relative to the remote workspace or local `lean/` mirror:
`logs/handoff-build.txt`, `logs/handoff-reproduction.txt`,
`logs/handoff-reproduction-packaged.txt`, `AuditAll.lean`,
`AuditAll.txt`, `Verification.json`, `SourceHashes.json`,
`Part2Checkpoints.json`, `Part2Coverage.json`, and `GoalRound7Preservation.json`.
`HandoffPreservation.json` checks the additional arrival snapshot.
The initial failed build is retained as `logs/handoff-arrival-build.txt`.
`handoff-checkpoint-logs.tar.gz` contains every log referenced by the
checkpoint manifest; the reproduction script restores these logs if needed.
