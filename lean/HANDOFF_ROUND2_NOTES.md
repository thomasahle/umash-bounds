# Round 2 continuation notes

## Accepted checkpoints

`published128 : Published128` is proved without an analytic premise, for the
original distinct-OH/two-independent-multiplier reference experiment. Its proof
commit is `5baffb5286ccd406a110fcafa87c16ddec877431`.

The two previously missing joint rows are closed:

- `subcase_b_bound : SubcaseBBound`, commit `9ecc08d`.
- `ph_one_word_enh_bound : PHOneWordENHBound` and
  `joint_block_bound : JointBlockBound1416246956032`, commit `d956894`.

The fingerprint proof uses the existing coarse primary marginal `364816/q`,
secondary `729632/q`, and joint bound below `2^-87`. It retains the two
identity events and their intersection, averages independent multipliers, and
conditions the OH tuple once. The rounding coefficient is below `7/10`.
The stronger `81/128` result is not claimed.

The new primary assembly isolates two analytic estimates in
`ProvenHashes/UMASHPrimaryHandoffObligations.lean`. These proposition definitions
are not axioms. The theorem `published64_of_primary_handoff` supplies the
complete remaining message classification, excluded-zero root saving,
conditioning, and rounding, from those two estimates.

## First analytic target: full blocks

Prove `PrimaryFullBlockBound256` exactly as defined: IID OH keys, valid blocks
of byte size 256, different chunk lists, primary projected collision at most
`256/q`. Full blocks have sixteen chunks and identical length tags.

The handoff route has two cases, both still requiring formal analytic work:

1. A PH chunk differs: the selected-bit conditional PH estimate below `164/q`.
   Source: `notes/02_primary_ph/proof.md`, especially §§2–5. It requires the
   carryless-polynomial gcd/kernel parametrization, rank of the conditional
   quadratic map, selected low/high bit pattern bounds, trie maximization,
   and their connection to an actual PH pair. The saved finite coefficients
   alone do not prove that connection.
2. Only ENH differs: average over at least three of the fifteen common PH
   chunks. Source: `notes/03_enh_envelope/proof.md`, §§3–4. The corresponding
   convolution/selected-pattern estimate gives less than `254/q`. Existing
   arbitrary-fixed-offset `3125/q` is insufficient here.

A sharper masked-PH statement can also discharge `PrimaryPHBound1123` and all
existing conditional 3125 assemblies. A larger full-block constant cannot
simply replace 256: the first published bucket uses the saved zero root and
has only about eight numerator units of slack.

## Second analytic target: literal last update

Prove `PrimaryLastUpdateBound503` exactly as defined: IID OH words and an
independent accepted multiplier in `{2,...,p-1}`, every valid distinguishing
block pair, actual `polyStep` equality with initial accumulator zero, strictly
less than `503/q`.

The statement is deliberately IID. The already-proved assembly applies the
OH distinctness correction once; `503/(q-561) < 512/q`. The handoff's sharper
intermediate coefficient `502/(q-24)` leaves sufficient room for this interface.

The new `polyStep_cancel_acc` and `hashWith_common_prefix_last_iff` reduce any
identical literal prefix to this zero-accumulator event. The common accumulator
may depend on every key and on the multiplier; no independence is assumed.
`polynomial_key_root_probability_zero_constant` saves the excluded zero root
on the exact multiplier sampler, without assuming exact polynomial degree.

The hard remaining case is an ENH-only change with both increments of the same
finite valuation at least four. Source: `notes/01_completion/proof.md`, §§3–6:

- Prove projection uniqueness on each actual wrap rectangle for A, B and
  the valid half-diagonals `(A+B)/2`, `(A-B)/2`.
- Use low equality to prove parity, and exclude exactly the zero-slope
  projections on each exceptional parameter line.
- Relate the literal high fold and actual byte tags to the seven normalized
  strip families, including the `255/q` tag allowance.
- Prove that the 288 off-line cells, 128 diagonal intervals, 16 anti-diagonal
  intervals and one intersection cover every normalized input pair.
- Prove soundness of outward polygons, merged projection intervals, and the
  integer lattice counts, then connect the 433 saved rational bounds to the
  actual event. Merely proving each saved value below 494 is insufficient.
- Weight the nonzero modular patterns by `gcd(|j|,8)/8`, use the actual modulus
  `8p`, and transfer the enlarged multiplier grid to the accepted sampler.

Unequal valuations and one-word changes avoid the geometric certificate but
still need the low-equality selected-pattern atom. The newly proved
`(2v+1)/q` high-XOR atom alone is too weak to replace that atom.

## Proof engineering

Do not replace accepted modules. New arguments are in new modules; the old
conditional interfaces remain intact. `staged/` contains matching theorem
sequences separated by `-- CHECKPOINT`; `stage-handoff.py` builds each prefix
using the cached Xeon project and stops on failure. Continue from the number
of accepted lemmas shown in its log, preserving the accepted prefix.

Run `bash reproduce-handoff.sh` for the root build, every-theorem axiom audit,
checkpoint coverage, and source-preservation checks. CPU affinity is 0–31,
16 Lean threads, nice level 10. Do not build on the Mac or rebuild Mathlib.
The complete checkpoint-log archive is included with the source mirror.

One subtlety: the legacy `enhValuation` takes `min (padicValNat 2 a)
(padicValNat 2 b)`, and `padicValNat 2 0 = 0`. For one-word changes use the
new `ChunkValuation` interface, which carries divisibility of both increments
and an explicit nonzero pivot. Do not silently change the old definition.

The historical exact-degree wording issue in `DEFECTS.md` is unchanged.
No additional false implication or counterexample to a claimed endpoint was
found in this round. The remaining gaps are unformalized analytic reductions.
