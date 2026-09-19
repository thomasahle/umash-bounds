# Goal-loop round 6: literal PH/ENH assembly and closed OpenPHENH

The continuation starts at `6585d4013fa56818233b2422bdac59e09e240528`.
All 187 pre-existing source modules remain byte-for-byte unchanged, and
all previous root imports are retained. `check-goal-round6.py` checks this.

## Closed results

`open_phenh_sharp : OpenPHENH` is now a closed theorem. Its precise target
is the original strict `2^-87` joint bound. The new proof actually covers
every positive minimum ENH valuation through 63, and a separate theorem
transfers that threshold to distinct OH keys. The stronger requested
PROOF2 constant `170906186782/q^2 < 2^-90` is still open.

The first obligation from round 5 is closed:

```lean
phenh_joint_ledger_reduction : PHENHJointLedgerReduction
```

This theorem applies to the literal block functions and carries no
analytic, independence, or shuffler premise. The reduction preserves
the exact low and high ledgers already defined in `UMASHJointLedger.lean`.

### Literal block algebra and target counts

`UMASHSinglePH.lean` proves unique-index decomposition when exactly one
nonfinal PH chunk differs. It proves both raw compressor identities,
the checksum relation between the changed PH and ENH input coordinates,
and cancellation of the common twisting product in the raw XOR.

`UMASHWordValuation.lean` identifies the valuation of a nonzero XOR with
the valuation of the wrapped additive difference. `UMASHENHTargetWords.lean`
translates independent additive keys into the operand model and transfers
the existing three-term ENH bounds to literal ENH outputs, with arbitrary
tags. Its low target retains precisely the positive-valuation premise.

`UMASHPHENHTargets.lean` supplies the low PH point count, the high PH
top-bit restriction, a product count on two different key coordinates,
and a general partition bound with a conditional twisting weight.

`UMASHShufflerSupport.lean` proves preservation of zero low bits at every
width, for both the shuffler and its inverse.

`UMASHPHENHAlgebra.lean` combines these facts. In particular,
`single_ph_joint_low_zero` proves literal equation (8) at `r >= 4`;
`single_ph_low_targets` and `single_ph_high_targets` identify the unique
PH and ENH targets for each pair of raw masks.

`UMASHPHENHProbability.lean` proves the two weighted finite-ledger bounds
and then `phenh_joint_ledger_reduction`. The high count retains the low
PH zero constraint, the equal-low-ENH constraint, and the high PH top-bit
filter. The twisting weight is conditional on all original chunk keys.
No independence between completed compressors is asserted.

### All 45 low-ledger cases

The original fifteen `r=3` cases remain unchanged. The new thirty cases
use uniform estimates, valid for every shuffler `s`:

```lean
phenh_low_ledger_small_certificate (r s : ℕ)
  (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
  phenhLowLedger r s ≤ 170906186782

phenh_low_ledger_certificate (r s : ℕ)
  (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hs1 : 1 ≤ s) (hs15 : s ≤ 15) :
  phenhLowLedger r s ≤ 170906186782
```

`UMASHJointLedgerLowCertificate.lean` checks the target ceilings
`34078720` and `67108864` over the 65 possible popcounts.
`UMASHTwistPopcount.lean` proves

```
W_L(v) <= min(1, |P(v)| * (h(v)+2) / 2^(h(v)+1)).
```

`UMASHLowWeightCertificate.lean` checks that the envelope sums are at
most 10 for valuation 1 and at most 4 for valuation 2. Thus the ledgers
are at most `169030451200` and `68719476736`, respectively. Both are
below the requested constant. `UMASHJointLedgerLowPopcount.lean` proves
the general finite-sum estimate; `UMASHJointLedgerLowFinal.lean` assembles
all low cases and supplies the conditional sharp theorem with only the
high-ledger inequalities as premises.

### Closed original OpenPHENH threshold

`UMASHOpenPHENH.lean` proves:

1. `highTargetK e <= 134217744` for every target `e`.
2. The exact high twisting weights sum to at most 18 over all 852 masks.
3. Every high ledger is at most
   `852 * 134217744 * 18 = 2058363321984`.
4. The literal joint probability is at most `2058363321984/q^2` for every
   positive ENH valuation through 63.
5. `open_phenh_sharp : OpenPHENH`, since that bound is strictly below
   `1/2^87`.

`UMASHOpenPHENHDistinct.lean` proves the strict 87-bit transfer to the
uniform distinct-key space using the existing acceptance estimate.
These results do not establish the stronger 90-bit constant or transfer.

## First remaining sharp obligation

It is now exactly the following finite proposition:

```lean
∀ s : Fin 15,
  phenhHighLedgerNumerator (s.val+1) ≤ 170906186782*q
```

The numerator is the following natural-number sum, with no rounding:

```lean
∑ u ∈ maskSet, ∑ v ∈ maskSet,
  if (phenhPHMask s u v).toNat < 2^63 then
    highTargetKNat (phenhENHMask s u v) * twistHighWeightNumerator v
  else 0
```

All definitions and exact bridges are in `UMASHLedgerInteger.lean`:

```lean
highTargetK e = (highTargetKNat e : ℚ≥0)
twistHighWeight e = (twistHighWeightNumerator e : ℚ≥0)/q
phenhHighLedger s = (phenhHighLedgerNumerator s : ℚ≥0)/q
```

`UMASHLedgerIntegerAssembly.lean` proves both the equivalence of each
integer inequality with the original rational inequality and:

```lean
joint_phenh_sharp_of_high_integer_certificate
  (hhigh : ∀ s : Fin 15,
    phenhHighLedgerNumerator (s.val+1) ≤ 170906186782*q) :
  JointPHENHSharpBound
```

The existing `phenh_distinct_of_sharp_joint` will then give the requested
strict 90-bit distinct-key transfer. No other block-model premise remains
in this part of the argument.

### Computation notes for the next continuation

Direct low-weight computations with the original `List.toFinset` mask
representation exhausted an imposed 12 GiB virtual-memory limit.
Rewriting with the already proved `maskSet_eq_fastCertificate` eliminated
the repeated quadratic deduplication; the two low sums passed in 15 seconds.

The high-weight sum uses a proved one-pass recurrence `highPrefixData` for
all prefix popcounts and their dyadic weights. Its integer certificate
passed in approximately 32 seconds under the same memory cap.

A full high-ledger computation for `s=1` exhausted the cap in both the
rational form and the first integer-form trial. Neither failed declaration
is retained in `ProvenHashes/`. The integer trial already rewrote the
inverse using the new width-uniform XOR-linearity theorem:

```lean
phShuffleInverse s (x ^^^ y) =
  phShuffleInverse s x ^^^ phShuffleInverse s y
```

A next implementation can certify and reuse the 852 inverse values per
shuffler, use a compact popcount recurrence for `highTargetKNat`, and split
the double sum into smaller checked rows. The reference Python ledger is
guidance for this calculation, not a Lean proof. In that reference ledger,
the largest high row is `s=2`, whose ceiling is exactly `170906186782`.

## Validation and reproduction

Every retained lemma has a successful `lake build` checkpoint. The stage
builder preserves each successful prefix and restores it when a candidate
fails. `Part2Checkpoints.json` records successful logs and their SHA-256s;
failed logs remain separately in the remote `logs/` directory.

`reproduce-part2.sh` performs the full build, emits `#print axioms` for
every local theorem, rejects prohibited constructs, and checks every
continuation-preservation baseline. Builds use the copied Mathlib cache,
`LEAN_NUM_THREADS=8`, and `nice -n 10 taskset -c 56-63` on the Xeon.

The complete requested project remains PARTIAL: the stronger PROOF2
constant, the closed 3125 all-pairs theorems, and both published headline
theorems remain listed precisely in the main status report.
