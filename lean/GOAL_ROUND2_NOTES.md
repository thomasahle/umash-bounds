# Goal-loop round 2: modular quadratics and accumulator arithmetic

This continuation starts from `c788f66`. Every pre-existing module under
`ProvenHashes/` is preserved byte for byte. `check-goal-round2.py` checks this,
and also checks preservation of every old root import.

## Complete PROOF2 Lemma 5.1

`UMASHQuadraticSets.lean` proves a stronger output-set statement. If either
coefficient `b` or `c` is odd and `2*m <= n`, then

```
quadraticSetCount n b c d T <= 4*T.card*(2^m-1) + 2^(n-m).
```

The base case is the cardinality of the input space. An odd linear
coefficient gives at most two roots per output, using the existing
`quadratic_odd_linear_parity_unique` theorem. Otherwise write `c=2*k`.
The even and odd input branches respectively satisfy

```
F(2*y)   = 4*(b*y^2 + k*y)     + d
F(2*y+1) = 4*(b*y^2 + (b+k)*y) + b+2*k+d.
```

After reduction modulo `2^(n+2)`, pull back the output targets under
`z |-> 4*z+v`. This map is injective on residues modulo `2^n`, so the
pullback has at most `T.card` targets. Each reduced input repeats twice.
Because `b` is odd, exactly one of `k` and `b+k` is odd. Its branch uses
the two-root theorem; the other uses induction. The exact recurrence is
`4*M + 2*(4*M*(2^m-1) + 2^(n-m))`.

For `T.card <= 2^(n-h)`, choose `m=h/2-1` when `h>=4`; smaller `h` uses
probability at most one. This proves `min(1,4/2^(h/2))`. The argument does
not need to classify odd squares and applies to every target set of that
size, not just to selected-bit sets.

`UMASHQuadraticBits.lean` injects each selected-bit target into its free
bits, giving at most `2^(n-S.card)` targets. It then proves
`quadratic_selected_bits_probability` and its `BitVec n` version with
the full PROOF2 hypotheses (including the even-linear, odd-quadratic case).

## Next mathematical obligation

`QuadraticIntervalCount` in `UMASHContinuationObligations.lean` is the exact
finite-preimage formulation of PROOF2 Lemma 4.1. It is still a proposition,
not a proved theorem. Its missing step is the aggregate interval-length
bound on both sides of the vertex; a separate square-root bound per value
interval would lose a factor depending on the number of intervals.

After that, PROOF2 still needs the line parameterization for the high ENH
event, all three terms of `K_H`, the low-target reduction and `K_L,r`, the
conditional twisting weights, and the sixty sums tied to literal blocks.
The new modular lemma discharges only Lemma 5.1, not those applications.

## Addendum foundations

`UMASHAccumulator.lean` proves the exact modulo-`q-8=8*p` equivalence:
for common raw lows and raw high difference `j*p`, equality after `polyStep`
is equivalent to `8 | f*j`. This survives word conversion and the bijective
finalizer, and applies after an arbitrary common literal prefix. The
square `f*f % p` from the original model is retained throughout.

`UMASHIndependentRoots.lean` proves the product of root bounds for two
independent `PolyKey` coordinates and arbitrary fixed comparison
polynomials, including zero polynomials. The averaging over OH identities
and message-level joint/marginal bounds are still missing.

`UMASHPublishedArithmetic.lean` proves the exact PROOF5 rounding certificate
`K < 81/128`, the PROOF4 coefficient comparisons, and the implication from
the proposed PROOF4 numeric envelope to the strict coefficient 58. None of
these arithmetic results establishes a collision envelope.

The continuation-obligations module also records the strengthened 64/128
targets, IID/nonzero-multiplier variants, block-swap lower bound, and the
secondary/joint block targets. They are definitions of propositions only.
