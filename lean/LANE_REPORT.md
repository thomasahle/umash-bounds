STATUS: PARTIAL

## DECISION (recorded before builds, 2026-09-19)

Continue **in place** in `<xeon>/lean-umash-corrected-2` with
ProvenHashes.UMASH, Lean 4.24.0, and the existing Mathlib cache. The handoff's
uncompiled 4.19 project leaves the same analytic interfaces open and would
duplicate the accepted implementation and probability development.
[COMPARISON.md](COMPARISON.md) records the model and vehicle comparison.

Round 2 resumed verified proof commit `a4ef141` and reporting commit `657e88d`,
preserving baseline `41d6558` and all uncommitted round-7 modules present on
arrival. All builds ran on the Xeon with `nice -n 10 taskset -c 0-31` and
`LEAN_NUM_THREADS=16`; the Mac was used for reading, editing and transfers.

**Result: `published128 : Published128` is proved unconditionally.**
`Published64` is still open. Its complete message assembly now reduces to
exactly the two analytic block estimates below. Neither requested proposition
was weakened. The 3125 all-pairs theorems still retain their PH premise.

## Remaining obligations

### 1. The primary published endpoint

The unchanged requested target is:

```lean
-- published64 : Published64
∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key64 => hash64 k seed x = hash64 k seed y) ≤
    ((L+511)/512 : ℕ) / (2:ℚ≥0)^55
```

The following sufficient reduction is now proved, including all message
branches, root counting, OH conditioning, and ceiling arithmetic:

```lean
published64_of_primary_handoff :
  PrimaryFullBlockBound256 → PrimaryLastUpdateBound503 → Published64
```

Its two premises are unproved proposition definitions in
[UMASHPrimaryHandoffObligations.lean](lean/ProvenHashes/UMASHPrimaryHandoffObligations.lean):

```lean
-- PrimaryFullBlockBound256: IID OH words
∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → x.byteSize = 256 → y.byteSize = 256 →
  x.chunks ≠ y.chunks →
  uniformProb (primaryEvent seed x y) ≤ (256:ℚ≥0)/q

-- PrimaryLastUpdateBound503: IID OH words, independent accepted multiplier
∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid →
  (x.chunks ≠ y.chunks ∨ blockTag seed x ≠ blockTag seed y) →
  uniformProb (fun k : OHKey × PolyKey =>
    polyStep k.2.val.val 0 (oh k.1 x seed) =
    polyStep k.2.val.val 0 (oh k.1 y seed)) < (503:ℚ≥0)/q
```

The first premise needs the handoff's conditional selected-bit PH estimate
below `164/q` and the common-PH convolution estimate below `254/q` for ENH-only
full blocks. Their algebraic rank/distribution reductions have not been
formalized. Existing arbitrary-offset `3125/q` does not meet the 256 target.

The second needs the literal mod-8p final-update count. Its hardest remaining
case has equal nonzero ENH increment valuations at least four. The supplied
433 saved rational cell bounds do not prove projection uniqueness, parity,
exceptional-line handling, polygon containment, continuous cover soundness,
or the connection to integer key counts and actual tags. Those missing
implications must be formalized before using the certificate. One-word and
unequal-valuation cases still need the low-equality selected-pattern atom.
No version of the handoff's unproved assertion (14) is assumed.

[HANDOFF_ROUND2_NOTES.md](HANDOFF_ROUND2_NOTES.md) gives the first analytic
attack, source sections, exact constants, and the reusable checked lemmas.
There is no environment or build blocker; these are remaining mathematical
formalization obligations.

### 2. The stronger 3125 and PROOF3/4/5 statements

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

These retain the stronger PROOF4/PROOF5 constants and their specified
sampler transfers; they do not follow just by renaming the new endpoints. PROOF5's stronger 81/128 result additionally needs the
3125 primary marginal; the original Published128 target is now proved using the
coarser marginal. No extra-premise theorem is called `published64` or
`published128`.

## Corrections

No requested endpoint or P1–P5 bound was found false. [DEFECTS.md](DEFECTS.md)
records one historical note's assertion of exact polynomial degree without a
nonzero leading coefficient. The corrected upper-degree statement suffices;
the consolidated paper already uses it. No new mathematical defect was found
in round 2.

The initial continuation repaired a delivery gap: `UMASHPHENHSharp.lean` was
imported by the root but existed only as a staging file. All nine closure
lemmas were compiled individually, retaining the fifteen ledger certificates.
This was a source-delivery issue, not a counterexample to the sharp bound.

## Milestones and signatures

The unconditional requested fingerprint endpoint is in
[UMASHPublishedFingerprint.lean](lean/ProvenHashes/UMASHPublishedFingerprint.lean):

```lean
published128 : Published128
-- Expanded unchanged proposition:
∀ (L : ℕ) (seed : Word) (x y : Message),
  1 ≤ L → x.length ≤ 8*L → y.length ≤ 8*L → x ≠ y →
  uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
    (((L+2^23-1)/2^23 : ℕ) : ℚ≥0)^2 / (2:ℚ≥0)^83
```

`Key128` uses 34 uniformly sampled distinct OH words and two independent
multipliers uniform on `{2,...,p-1}`. The theorem covers every short/long
combination, equal and unequal block counts, byte-length tags, ENH's high-XOR-low
fold, and the literal mod-8p accumulator.

Other closed declarations include:

```lean
joint_phenh_sharp : JointPHENHSharpBound
subcase_b_bound : SubcaseBBound
ph_one_word_enh_bound : PHOneWordENHBound
joint_block_bound : JointBlockBound1416246956032
secondary_block_bound : SecondaryBlockBound729632
different_checksums_bound : DifferentChecksumsBound
joint_tag_only_bound : TagOnlyBound
closed_ph_two_word_enh_bound : ClosedPHTwoWordENHBound
one_word_enh_bound : OneWordENHBound
closed_two_word_enh_bound : ClosedTwoWordENHBound
```

`joint_phenh_iid_lt90` and `joint_phenh_distinct_lt90` retain PROOF2's strict
90-bit bounds; `phenh_sixty_case_maximum` certifies its exact sixty-case maximum.
The existing ENH-only 3125 and sharp primary tag-only results are retained.

Round 2 additions:

- The two-PH row uses literal shuffler elimination and three compatibility
  bits. Rational square bounds separate the low/high sums without assuming
  lane independence; the final numerator is at most `1400832000000`, below
  the required `1416246956032`.
- The one-word high-XOR atom is width-uniform, counted by affine-XOR
  injectivity and dyadic bins: `(2v+1)/q`, at most `127/q` at width 64.
  The exact even-mask twisting-weight sum is at most 6, giving the low ledger
  `101418270720 < 2^37`. The unchanged one-word row target is `2^-91`.
- The fingerprint assembly uses primary marginal `364816/q`, secondary
  `729632/q`, and joint probability below `2^-87`; its exact rounding
  coefficient is below `7/10`. No stronger `81/128` coefficient is claimed.
- Joint message identities use a common distinguishing block for both modes.
  Unequal lengths use the same leading zero block, bounded by `24354/q²`.
  Short/long identities force two short constants to zero, bounded by `81/q²`.
  The short/short actual collision bound is `1/(q*(q-561))` after conditioning.
- `polynomial_key_root_probability_zero_constant` saves the excluded zero
  root without asserting exact degree. `polyStep_cancel_acc` and
  `hashWith_common_prefix_last_iff` cancel a common literal accumulator even
  when it depends on the full key and multiplier.
- `primary_other_counts_published` and `primary_short_long_published` prove
  those primary headline branches unconditionally. The equal-count
  classifier and `published64_of_primary_handoff` leave only the two stated
  block estimates.

Every previously accepted primary, ENH-only, IID, linear, inheritance,
accumulator, shuffler, tag-only, and reference-swap theorem is retained.

## Axioms, commits, and reproduction

Workspace: `<xeon>/lean-umash-corrected-2` on the Xeon. Complete Lean source
mirror: `lean/`. Lean 4.24.0; Mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

The final root `lake build` passes: **8093 jobs**. The complete `#print axioms`
audit passes for **1585 theorem/lemma declarations**, with only `propext`,
`Classical.choice`, and `Quot.sound`. The source scan finds no `sorry`, `admit`,
`native_decide`, custom axioms, or unsafe declarations.

Per-lemma coverage passes: 454 parent declarations and 1131 later declarations,
1143 successful checkpoints, none missing. All 203 baseline modules remain
byte-for-byte unchanged; all baseline imports remain. The separate arrival
check preserves all 687 modules present on arrival, including uncommitted
round-7 work. Round 2 adds 141 audited theorems in total.

Accepted proof commits:

- `41d6558609f9406b0405171636097d0949749461`: original verified baseline.
- `a4ef141046a57e14eb1caf3c24c508c06feb3d56`: sharp ledger and initial joint cases.
- `9ecc08d12770f16e54180bc923dec8dc5166f076`: unconditional two-PH row.
- `d956894228eba94b61ebc512acf786e6687ad3cd`: one-word row and joint block bound.
- `5baffb5286ccd406a110fcafa87c16ddec877431`: unconditional `published128`.
- `115d1ee18b680645aeaed1885d77033fa6d1558d`: complete primary reduction and final audit.

Reproduce on the cached Xeon workspace:

```bash
bash reproduce-handoff.sh
```

The script checks the pinned toolchain and cached Mathlib artifact, runs the
root `lake build`, audits every theorem with `#print axioms`, and checks every
per-lemma log and preservation manifest. No Mathlib source rebuild is used.

Evidence paths, relative to the workspace or `lean/` mirror:
`logs/handoff-build.txt`, `logs/round2-final-reproduction.txt`,
`logs/round2-published128-reproduction.txt`, `AuditAll.lean`, `AuditAll.txt`,
`Verification.json`, `SourceHashes.json`, `Part2Checkpoints.json`,
`Part2Coverage.json`, `GoalRound7Preservation.json`, and `HandoffPreservation.json`.
`handoff-checkpoint-logs.tar.gz` contains all logs referenced by the current
checkpoint manifest; reproduction restores them if needed.

The checkpoint archive has 1143 unique logs; `CheckpointArchive.json` records
its SHA-256. `Commit.txt` identifies the final proof commit; subsequent
reporting commits change documentation and commit metadata only.
