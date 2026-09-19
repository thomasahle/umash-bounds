# Goal-loop round 4: dense high ENH and the low-target elementary bounds

This continuation starts at `b3e613e`, whose proof-source commit is
`0aa58dc`. Every pre-existing module and root import is preserved;
`check-goal-round4.py` checks that baseline byte for byte.

## Closed: the first recorded obligation

`high_enh_dense_bound : HighENHDenseBound` is a theorem with no analytic
premise. The stronger width-uniform theorem needs only a nonzero first
increment, an in-range second increment, and arbitrary natural tags:

```lean
high_xor_dense_probability (n δ ε tag tag' e : ℕ)
  (hδ : 0 < δ ∧ δ < 2^n) (hε : ε < 2^n) :
  uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
    highTaggedXorEventNat n δ ε tag tag' e (ab.1.val, ab.2.val)) ≤
    (4*n+20:ℕ)*(2:ℚ≥0)^(n-(maskBitSet n e).card)/(2:ℚ≥0)^n
```

It does not require equality of the low product words. At width 64,
`4*n+20=276`. The proof follows the product-sum argument:

1. `dyadic_reciprocal_sum` bounds the sum over positive words by n. Its
   induction splits the range at `2^n`; each new dyadic interval costs one.
2. `reciprocal_sum_pair_bound` proves the two-positive-operands inequality
   and includes explicit indicators for either operand being zero.
   `sum_range_wrapped_add` permutes the translated summand.
   `wrapped_reciprocal_sum` therefore gives `n/2+2`, including zero operands.
3. `nat_affine_interval_count` counts integer inputs in an interval of a
   positive-slope affine map. `product_high_sum_interval` bounds the full
   product sum between `Q*t` and `Q*t+2*Q`, without a low-word equality.
4. Each fixed A and sum residue has two B wraps and two high-sum integer
   representatives. `wrapped_high_sum_fiber_count` bounds their union by
   `4*(2*Q/(A+A')+1)`. Summing gives `(4*n+20)*Q` pairs per residue.
5. The common pattern `U AND U'` vanishes on the XOR mask e. The existing
   selected-bit cardinality theorem supplies at most `2^(n-h(e))` patterns.
   Arbitrary tags are removed by modular addition cancellation, after
   deriving the actual tagged-sum congruence.

`high_enh_target_bound` combines the dense result with the preserved sparse
and quadratic results. It proves the complete three-term `highTargetK`,
exactly PROOF2 (14), for the literal common-low/high-XOR event. Neither
this theorem nor the individual high-target estimates needs a valuation
premise. This milestone was committed as `5089c91`.

## Closed: the elementary parts of PROOF2 Lemma 5.2

`low_xor_zero_probability` proves exact equality `2^r/q`, where r is the
actual minimum valuation of the two nonzero increments. The proof uses
the existing exact additive distribution and the equivalence between
equal low product words and zero additive difference.

`low_xor_sparse_probability` proves

```
Pr[lowENHXor=e] <= 2^r * 2^(h(e)-topBit(e)) / q.
```

It keeps the top-bit saving: doubling a sign pattern makes its top bit
irrelevant modulo `2^64`. The union is indexed by `submaskTargets 63 e`,
whose cardinality is at most `2^(h(e)-topBit(e))`. The minimum-valuation
orientation and swapping of the actual word coordinates are proved.

`low_xor_dense_probability` proves

```
Pr[lowENHXor=e] <= 65 * 2^(64-h(e)) / q.
```

Here only even increments and an even target are needed at the operand
level. `low_xor_half_product_target` proves PROOF2 (20) over `ZMod (2^63)`.
Common bits give the complementary-mask target count. The product point
bound is proved at every width by `modular_product_count`:

```lean
2*S.card ≤ (n+2)*2^n
```

for any finite set of pairs below `2^n` with a common product residue.
Induction separates odd and even first operands. Odd first operands
permit at most one second operand each. Even first operands reduce to
the preceding width and have two high-bit lifts of the second operand.
The base case is width zero. Translation and independent high-digit
reduction are proved separately, giving `65/q` at width 63 on the actual
64-bit words. No full-word key space is enumerated.

## Progress toward the quadratic low-target term

`UMASHLowCoordinates.lean` proves the following remaining ingredients
of the change of variables:

- `low_coordinate_bijective`: `(A,B) -> (A,aB+bA+Rab)` is bijective modulo
  any power of two when a is odd.
- `low_coordinate_quadratic_identity`: `aAB=-bA²+(C-Rab)A`.
- `low_coordinate_difference_identity` and
  `low_coordinate_event_congruence`: the actual low-XOR event fixes
  `R*C` to `e-2z` modulo the word size.
- `signed_submask_exact_valuation`: for nonzero e and `z AND e=z`, the
  signed integer `e-2z` has exactly e's valuation, including negative values.
- `low_coordinate_exact_valuation`: every coordinate lift C therefore
  has exact valuation `v₂(e)-r`.
- `low_coordinate_common_factor_bound`: if `2^s` divides both quadratic
  coefficients b and `C-Rab`, then `s+r <= v₂(e)`. This is the portion of
  PROOF2 (19) needed to retain all selected bits after division.
- `scaled_coordinate_lift_count`: at most `2^r` coordinate lifts C satisfy
  one fixed scaled residue equation modulo `2^n`.

## First remaining analytic proposition

`LowENHQuadraticBound` in `UMASHRound4Obligations.lean` is a checked
definition of a proposition, not an assumption in any closed bound:

```lean
∀ (δ ε r e : ℕ),
  0 < δ → δ < q → 0 < ε → ε < q →
  r = min (padicValNat 2 δ) (padicValNat 2 ε) →
  1 ≤ r → 0 < e → e < q → 2^r ∣ e →
  uniformProb (fun ab : Word × Word =>
    lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
    (4:ℚ≥0)*2^r*2^(((maskBitSet 64 e).card+1)/2)/q
```

What remains is a finite count on each fixed `(C,z)` fibre. After choosing
the minimum-valuation increment `δ=R*a` with a odd and writing `ε=R*b`,
normalize the polynomial `a⁻¹*(-bA²+(C-Rab)A)` by its greatest common
power `2^s`. Its normalized quadratic or linear coefficient must be odd.
The proved common-factor bound puts every selected bit of e above s.
Formalize the shift of those selected positions into width `64-s`, prove
that uniform A reduces uniformly to that width, then apply
`quadratic_selected_bits_probability` (or the stronger
`quadratic_small_set_count`). This must give at most
`4*q/2^floor(h(e)/2)` values of A per fixed `(C,z)` fibre. The bijection
recovers B uniquely; sum the `2^r` lifts and `2^h(e)` patterns and simplify
the exact powers. Handle both orientations using `low_xor_probability_swap`.

The checked theorem

```lean
low_enh_target_bound_of_quadratic : LowENHQuadraticBound → LowENHTargetBound
```

shows that this is the only missing analytic term of Lemma 5.2. It is
explicitly conditional and is not reported as a proof of that lemma.

After it, the conditional twisting-checksum weights, literal block
decomposition, Lemma 6.1, and all sixty exact shuffler sums still need their
proofs. No final `OpenPHENH`, 3125 all-pairs, `Published64`, or
`Published128` closure is claimed. All remaining tasks in STATUS.md remain
part of the original goal.
