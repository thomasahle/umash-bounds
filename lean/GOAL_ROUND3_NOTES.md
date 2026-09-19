# Goal-loop round 3: interval packing and high ENH targets

This continuation starts from `8d79137`, whose proof-source commit is
`f61ef42`. All 161 pre-existing source modules are preserved byte for byte;
`check-goal-round3.py` checks that baseline and every original root import.

## Closed: PROOF2 Lemma 4.1

`quadratic_interval_count : QuadraticIntervalCount` proves exactly the
previously recorded obligation. No analytic premise was added.

The proof uses finite packing, without integration. For nonnegative,
pairwise ordered spans `[l_i,u_i]`, it proves

```
(sum_i (u_i-l_i))^2 <= sum_i (u_i^2-l_i^2).
```

For strictly positive spans, induction removes the rightmost interval.
The same induction proves that all preceding widths total at most its
left endpoint. That gives the cross term needed when squaring the sum.
Singleton spans contribute zero and are filtered out in the general lemma.
For each output interval and each side of the vertex, take the least and
greatest integer preimages in the given finite set. Their span contains
at least `card-1` units of length. Disjoint output intervals give ordered
input spans, also for a negative leading coefficient. The squared-endpoint
budget is `m*ell/abs(a)`. Sum first, take the square root once, reflect the
left branch by integer negation, then complete the square. The vertex can
occur in both branches; the requested `2*m` allowance covers it.

## Closed: PROOF2 Lemma 4.2, integer-ceiling form

`high_xor_quadratic_probability` proves the bound at every word width n.
`high_xor_quadratic_probability_word` specializes to the actual 64-bit
`Word` type and exact rational `uniformProb` convention:

```
Pr[L=L' and U xor U'=e] <= 16*(2^ceil(h/2)+1)/q,
h = (maskBitSet 64 e).card.
```

Here `highXorEventNat` expands the literal wrapped ordinary products and
tag additions. Both increments must be nonzero and smaller than q. Tags
are arbitrary naturals. No positive-valuation or r>=4 premise is used.
The selected positions in `maskBitSet` are exactly the true bits of e
among the n word positions.

The implementation follows these checked steps:

1. `coprime_line_coordinate` recovers the line parameter explicitly as
   `(x-x0)/a` after primitive normalization. Products along that line have
   leading coefficient `-a*b`. General signed increments are divided by
   their gcd, so the new leading coefficient has absolute value at least 1.
2. `wrappedProductBranch` records each operand's wrap quotient and the
   product difference divided by q^2. The three coordinates lie in
   `{0,1}`, `{0,1}`, and `{-1,0}`. The target set has exactly eight elements.
   A fixed residue and branch determine one integer line. Zero operands
   and negative product differences remain covered.
3. `wrapped_product_high_set_count` proves, for any finite high-word target
   set H, the bound `16*(sqrt(H.card*q)+H.card)` on a residue fibre.
   Its disjoint product intervals are `[q*H,q*(H+1))`.
4. `high_xor_product_residue` proves equation (12), with all tag wraps,
   using the low-word equality and the actual integer XOR-difference identity.
5. `mask_value_targets_card_le`, `submask_targets_card_le`, and
   `tagged_mask_targets_card_le` give at most `2^(n-h)` high-word targets
   per pattern and at most `2^h` patterns. Tags act by an explicitly
   injective translation modulo `2^n`.
6. `dyadic_high_pattern_bound` and `dyadic_high_pattern_sum` prove the
   square-root rounding and exact power identity. The final finite count
   is `16*(2^ceil(h/2)+1)*2^n`. Dividing by the actual key-space cardinality
   gives the rational probability theorem.

## Closed: a stronger sparse term of PROOF2 Lemma 4.3

`high_xor_sparse_probability` and `high_xor_sparse_probability_word` prove

```
Pr[L=L' and U xor U'=e] <= 2^h/q.
```

They reuse `wrapped_product_difference_unique`, the already proved
cross-wrap injectivity of the full product-difference residue for fixed A.
An event pair is recovered from `(A,U & e)`. This is no larger than the
requested `2^(1+h-topBit(e))/q`, and needs only the first increment to be
nonzero. It does not change or replace any of the existing 364816 results.

## First remaining analytic statements

The checked definitions `HighENHDenseBound` and `LowENHTargetBound` in
`UMASHRound3Obligations.lean` are propositions only, not assumptions or
proofs. The next target is `HighENHDenseBound`: the coefficient
`276*2^(64-h)/q` for the high tagged XOR event **without** requiring equal
low words.

A direct route to that proof is to formalize PROOF2 Lemma 4.3's product-sum
argument. The mask allows at most `2^(64-h)` high sums modulo q. Each has
at most two integer high sums; each B-wrap gives an affine product sum
with positive slope `A+A'`. An interval of length `2*q` has at most
`2*q/(A+A')+1` integer preimages. The reciprocal sum over A must be proved
at most 34, treating A=0 and A'=0 separately and bounding the positive
harmonic sum by 64 using dyadic intervals. The resulting total is 276*q
pairs per prescribed sum. The selected-bit counting lemmas from this
round can be reused for the complementary mask.

After this, prove `LowENHTargetBound` (all three terms and the zero target),
including the valuation division in equation (18), then the conditional
checksum weights and the sixty sums, with the literal block decomposition.
The exact final numeral `phenh_sharp_arithmetic` still does not certify
those sums. No new proof of `OpenPHENH`, the 3125 all-pairs theorem,
`Published64`, or `Published128` is claimed in this round.
