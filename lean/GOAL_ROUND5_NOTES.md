# Goal-loop round 5: the low quadratic term and conditional checksum weights

The continuation starts at `48ceeee`. All 179 pre-existing source modules
are preserved byte for byte, and all previous root imports are retained.
The preservation check is `check-goal-round5.py`.

## Closed first obligation: PROOF2 Lemma 5.2

`low_enh_quadratic_bound : LowENHQuadraticBound` and
`low_enh_target_bound : LowENHTargetBound` are now closed theorems.
The first milestone is commit `c5614c9d8071f6ac720e0c417171721bcdfe1175`.

`UMASHDyadicNormalization.lean` supplies four ingredients:

1. `dyadic_primitive_factor` factors two integer coefficients into a common
   power of two and a primitive pair, including zero coefficients.
2. `mask_bit_set_div_pow_card` proves that removing zero low mask bits
   preserves the number of selected positions.
3. `quadratic_small_set_lift_count` lifts the existing primitive quadratic
   count from width `n-s` to width `n`, keeping the `2^s` high input lifts.
4. `scaled_quadratic_mask_count` transports the selected-bit target set
   through an odd multiplier. The normalized target set has at most
   `2^(n-s-h)` elements; it is not necessary to choose an inverse multiplier.

`UMASHLowTargetQuadratic.lean` applies these to the already proved
coordinate identities. A fixed coordinate `C` and pattern `z` admit at
most `4*2^(n-floor(h/2))` pairs. The odd coordinate multiplier makes the
first operand injective on such a fibre. The common-factor bound retains
all selected bits. Summing the `2^r` coordinate lifts and `2^h` patterns
gives `4*2^r*2^ceil(h/2)/2^n`. Both minimum-valuation orientations are
handled on the actual 64-bit word operands.

The quadratic term itself does not require `r >= 1`. The complete
`low_enh_target_bound` retains exactly the requested `r >= 1`, because
the separately proved dense term uses even increments.

## Closed: PROOF2 Lemma 3.2 on the literal secondary slices

`UMASHPHSelected.lean` proves the high and low selected-bit counts for
carryless multiplication. The high proof reconstructs input bits from
the highest differing bit; the low proof uses the lowest differing bit.
In both cases the unselected input bits inject each output fibre into a
Boolean function space, giving the exact bound `2^(64-h)`.

`UMASHPHWeights.lean` counts the multiplier degree and valuation classes,
keeps the zero multiplier separately, and averages the selected-bit bounds.
It defines `twistHighFactor` and `twistLowFactor`, the exact rational
functions in PROOF2 (9), without negative powers.

`UMASHTwistWeights.lean` proves the pattern union bound and clips it at one.
XOR translation by a fixed checksum preserves the two independent
twisting operands. `checksum_code_split` and
`checksum_eq_of_data_checksum` establish equality of the literal keyed
checksums from equal data checksums and equal chunk counts.

The final `secondary_twist_high_weight` and `secondary_twist_low_weight`
theorems hold on `ohSecondary (keyPairsEquiv.symm (Function.update K 16 v))`.
They fix all 32 original word keys, leave the two twisting words uniform,
and retain the two different fixed secondary-body offsets. They do not
assume independence between completed compressors or between their lanes.

## Closed: executable shuffler inversion

`UMASHShufflerInverse.lean` uses the recurrence `x_(m+1) = y XOR S(x_m)`.
Strictly positive shifts make each step stabilize one additional low bit.
After `n` steps it is a two-sided inverse of `I+S` on `BitVec n`.
`shuffler_elimination_explicit` proves PROOF2 (7) using this executable
inverse, without a noncomputable inverse witness.

## Exact remaining PROOF2 assembly

`UMASHJointLedger.lean` defines the literal finite sums `phenhLowLedger`
and `phenhHighLedger`, using `lowTargetK`, `highTargetK`, the proved
twisting weights, and the executable inverse. The high sum explicitly
filters the high PH mask to `<2^63`.

Two checked proposition definitions isolate the remaining work:

- `PHENHJointLedgerReduction`: for every valid equal-count,
  equal-checksum block pair with one changed PH chunk and both ENH words
  changed, and valuation in `[1,63]`, some shuffler `s` in `[1,15]` bounds
  the actual joint event by the corresponding ledger divided by `q^2`.
- `PHENHJointLedgerCertificate`: the low sums for `r=1,2,3` and all fifteen
  shufflers, and the high sums for all fifteen shufflers, are at most
  `170906186782`.

`UMASHJointLedgerCertificate.lean` already proves
`valuationMasks_three_exact` and `phenh_low_ledger_r3_certificate`.
The latter checks all fifteen `r=3` sums against the sharper row ceiling
`268435521`, using `decide +kernel` on the exact rational expressions.
Those fifteen cases are closed. The thirty low cases for `r=1,2` and the
fifteen high cases remain to be checked; Python certificate results alone
are not treated as Lean proofs.

The first still requires the literal one-PH block decomposition, equality
of the PH coordinate XOR increments and the final ENH increments from the
data checksum, the valuation transfer to wrapped additive increments,
independent PH/ENH key counts, support of both raw masks in
`valuationMasks r`, preservation of their low zero bits by the inverse,
and the conditional weight summation.
Use `oh_code_sum`, `secondary_twist_slice`, the new checksum equality,
`ph_xor_target_probability`, `low_ph_distribution`,
`phenh_low_reduction`, `high_enh_target_bound`, and `low_enh_target_bound`.
No analytic ENH bound or checksum-weight lemma remains as an assumption.

`joint_phenh_sharp_of_ledger` assembles the requested sharp proposition
with precisely these two premises explicit. It is not a closed proof of
`JointPHENHSharpBound` or `OpenPHENH`.

All PROOF3, PROOF4, and PROOF5 final closures listed in `STATUS.md` remain
part of the goal. The existing 364816 theorems and the literal modulo-8p
accumulator are unchanged.
