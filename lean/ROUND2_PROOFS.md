# Round 2: carry-less multiplication, rank, and the PH block bound

These are formalizations of paper-proved results. They do not close either
open ENH case or establish the sharp primary projection premise.

## Literal multiplication and PH injectivity

`UMASHCarryless.lean` defines `bitPolynomial` by assigning a word's bit i to
the coefficient of X^i over `ZMod 2`. It proves coefficient equality,
injectivity, XOR/addition compatibility, and the exact shift identity when
zero extension leaves sufficient room.

`bitPolynomial_clmul` proves that the existing 64-iteration `clmul` loop
computes polynomial multiplication. Every shifted operand fits in 128 bits;
no replacement hash model or unproved equivalence is used. Integral-domain
cancellation gives `clmul_left_injective`. The two XOR distributivity
identities then prove `ph_xor_slice_injective : PHXorSliceInjective`.

`ph_slice_projected_bound` composes this injectivity with the previously
checked 852-mask certificate, allowing arbitrary fixed 128-bit XOR
contributions on both sides and an arbitrary translated free key word.

## Shifted-product fibre count

`UMASHRank.lean` proves `rank_lemma64 : RankLemma64` by counting fibres
directly. For nonzero d, let v be the first nonzero coefficient index of
`bitPolynomial d`. An input position i is discarded exactly when

```
64 - h <= (v + i) % 64.
```

The finite set `discardedBits v h` has at most h elements: its elements
inject into `Finset.range h` via `(v+i)%64 - (64-h)`.

Suppose two keys in the same shifted-product fibre agree on all discarded
positions but are different. Let t be the first differing input bit.
The coefficient at v+t of the product of d and the XOR of the two keys is
nonzero, by the polynomial trailing-coefficient multiplication theorem.
Since t is not discarded, that coefficient is retained by the lane shift.
Equality of the shifted outputs says it is zero, a contradiction.

Thus the discarded bits inject each fibre into a Boolean function space of
cardinality at most 2^h. This proves the original bound for every h <= 64,
including h=0 and h=64, without postulating a matrix rank computation.

## Complete OH block with a differing PH chunk

`UMASHBlockPH.lean` represents each output chunk by its pair of binary
polynomials. This representation is injective and sends chunk XOR to
addition. `oh_code_sum` proves the resulting sum formula for the literal
`mixed` list, including its final ENH term.

`exists_differing_ph` selects a genuinely differing nonfinal chunk from
`phDiffCount > 0`. `ph_key_update_injective` selects the opposite key word
from a differing data component. Validity bounds the number of chunks by
16, so `keyPair_update_other` proves that every other chunk's keys are
unchanged. `oh_update_code_constant` isolates the selected PH term and a
constant remainder, separately for each of the two blocks.

The selected PH difference is injective, constant contributions cancel,
and the 852-mask transfer bounds each one-word key slice by 852^2/2^64.
`probability_le_of_update` proves the exact averaging over all 34 uniform
OH words. The final result is `primary_ph_bound : PrimaryPHBound`, with
the original proposition and its literal `oh` and `project` functions.

All top-level lemmas have individual `lake build` checkpoints. Their proof
dependencies are included in `AuditAll.lean` and `AuditAll.txt`; no claim
rests on the informal explanation in this file.
