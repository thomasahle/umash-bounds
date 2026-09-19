# Comparison of the supplied UMASH arguments

The model and vehicle comparison was written from local source reading before
any build in this continuation. Formalization results are appended below.
The formalization vehicle is ProvenHashes.UMASH. No existing theorem or
probability definition is weakened.

## Sources and page convention

`H` below means `../../umash-handoff/umash_codex_handoff/`. Paper page numbers
are its printed Arabic pages (the PDF also has a cover and front matter).
`P1` through `P5` mean `../../umash-goal/PROOF.md`,
`../../umash-goal2/PROOF2.md`, `../../umash-goal3/PROOF3.md`,
`../../umash-goal4/PROOF4.md`, and `../../umash-goal5/PROOF5.md`.
These are local relative source references, not claims of publication.

The reading includes the handoff's README, brief, author review, status,
36-page paper and LaTeX, note-directory reading map, mathematical notes,
geometry checker, and Lean specification/experiment/classifier/analysis
interfaces. Retained numerical outputs are evidence of their stated
calculations, not independent proofs of their analytic reductions.

The prior verdicts are `../../../design/umash-verify{,2,3,4,5}/VERDICT.md`.
Their accepted bounds are preserved. In particular, P5's two imported
joint-case dependencies have separate confirmed reviews; its verdict
explicitly distinguishes these from the later multi-lens review.

## Construction and experiment

| Detail | Handoff | P1–P5 / ProvenHashes | Conclusion |
|---|---|---|---|
| Word and field sizes | q=2^64, p=2^61-1 | Same | Identical |
| Primary multiplier | Uniform {2,...,p-1}, cardinality p-2 | Same | Identical; excluding only zero would change the sampler |
| OH sampling | 34 IID words, then condition the whole tuple on injectivity | Uniform ordered distinct tuple; IID theorems proved first | Same finite law by equal weights of injective tuples; no post-conditioning coordinate independence |
| Fingerprint multipliers | Two independent accepted multipliers sharing OH | `Key128` has two independent multipliers | Same architecture |
| Literal Python key record | Only one `poly` field; explicitly excluded if reused for both modes | P5 §11 proves its block-swap obstruction | The two-multiplier extension is necessary; unqualified “the Python fingerprint” is ambiguous |
| C multiplier range | Main theorem uses the reference range | P5 additionally allows {1,...,p-1} | P5 covers a further ideal sampler; neither analysis proves the production key-expansion law |
| ENH | Ordinary product; add high tag; XOR low into high | Same | Identical; unfolded NH would be a different construction |
| Tag | seed XOR (original block byte count mod 256) | Same | Equal upper 56 bits; signed gap at most 255 |
| Accumulator | `((f*f % p)*(acc+lo)+f*hi) % (8*p)` | `polyStep` uses modulus q-8=8*p and the same reduced square | Identical |
| Short dispatch | Length at most 8; secondary noise index shifted by 4 | Same | Must handle overlapping noise indices |
| Byte expansion | First/last 8 for 9–15 bytes; overlapping final 16-byte chunk otherwise | Same | Preserve original byte contributions when tagging |
| Probability type | Finite rational conditional law on `Fin` words | Exact cardinality ratios in ℚ≥0 with `BitVec` words | Representation difference, not a different experiment |
| Length variable | Byte cap s | Word cap L, bytes at most 8L | Set s=8L: ceiling buckets match exactly |

Sources: H paper §§1.1–1.5, pp.1–3, Remark 1.1; H
`lean/Umash/{Reference,Experiments,Goals}.lean`; P4 §§1–2; P5 §§1,3,11;
`lean/ProvenHashes/{UMASHModel,UMASHObligations,UMASHContinuationObligations}.lean`.
This is a comparison of mathematical definitions and source structure, not
a new formal equivalence proof between the two Lean projects or a C binary.

## Bounds and constants

All block numerators below are for IID OH words. Distinctness costs at most
one division by ρ=1-561/q for the entire event. Let m=p-2 and r*=2^19/m.

| Quantity | Handoff | Our supplied proof | Assessment |
|---|---|---|---|
| Primary fixed projected target | a*=81(2/q-1/q²)<162/q | P1 Lemma 6.3: (82q-81)/q²<82/q | Both valid; ours counts at most one zero-product preimage, instead of charging its larger mass 81 times |
| Secondary fixed projected target | a*<162/q | P5 §6: (46q-45)/q²<46/q | Ours also uses the carryless product's zero top bit (45 possible targets) |
| Joint fixed targets | a*²<26244/q² | P5 §6: <82·46/q² | Both are conditional fresh-twist arguments; neither proves a same-key pairwise bound |
| PH-changing primary block | <164/q | P3 ≤1123/q; P4 ≤151/q | Different valid upper estimates, not incompatible collision counts |
| ENH-only with common PH | <420/q with one PH, <267/q with two, <254/q with three | P4 <205/q with one PH; P3 ≤3125/q with arbitrary common offset | Different estimates; P4 is sharper with a PH mask; H's three-PH bound covers full blocks |
| Primary tag-only | <208/q | P2 Theorem 9.2: <1/(8q) | Ours is much stronger: ≥54 selected bits, ≤8 patterns, and d(N)<2^36 rather than the looser cube-root divisor estimate |
| High-valuation last update | Identity-and-update coefficient <494 under enlarged multiplier grid; actual bound <502/((q-24)ρ)<503/q | P4: <435/q identity-and-update under accepted multipliers, then +2/m and OH correction | H permits any common PH mask; P4's special count is for a one-chunk final block. These are not identical intermediate events |
| Two changed PH chunks, equal checksum | 345763417/2^116 | Same, J/q², J=1416246956032 | Exact agreement; h=15 binds the table |
| One PH + two ENH words | Overall (213/256)·2^-87; high table peaks at 0.702595…·2^-87, shuffler T+T^4 | P2: 170906186782/q²<2^-90 for every positive valuation | Ours is sharper and uses a different high-XOR estimate; different maximizing shufflers are expected |
| ENH-only joint | High case 4721784/q²; low cases looser | P1: 4721784/q² for all valuations | H retains older, looser low-case counts |
| Overall primary marginal for fingerprint | 852²/q=725904/q | P1 364816/q; P3 3125/q | Coarse marginals suffice for H's endpoint |
| Overall secondary marginal | 2·852²/q=1451808/q | P5 2·604²/q=729632/q | Ours retains fixed lane-bit constraints |
| Overall joint block | (213/256)·2^-87=1829656068096/q² | P5 J/q²=1416246956032/q² | H's bottleneck is its middle-valuation PH+ENH estimate; ours is the two-PH row |
| Primary endpoint | <ceil(s/4096)·2^-55 | P4 <58·ceil(L/512)/2^61 | P4 is stronger; same headline at s=8L |
| Fingerprint endpoint coefficient | Exact arithmetic ratio 0.8116054534912109… at the first bucket | P5 ratio 0.6276036008493975… <81/128 | P5 is stronger; H still fits below 1 |

H references: §§2.2–2.3 pp.3–4; §§4–5 pp.8–14; §6 pp.14–18;
§8 pp.19–25; §9 pp.25–27. Detailed sources are
`notes/02_primary_ph/proof.md` §§2–6,
`notes/03_enh_envelope/proof.md` §§3–4,
`notes/01_completion/proof.md` §§3–7,
`notes/04_joint/joint_compressor_proof.md` §§4–7, and
`notes/05_fingerprint/end_to_end_proof.md` §§2–7.

The original fiber-size inference remains invalid as a generic inference:
take deterministic distinct outputs u and v in the same reduction fiber.
Their raw collision probability is zero and their reduced collision
probability is one. A raw pairwise equality bound cannot be multiplied by
the maximum fiber size to repair this. Both sets of proofs explicitly avoid
that step (H §2.3 p.4; P1 §§3–6). This refutes the inference, not the
published endpoint. H's auxiliary (14) is separately unproved and unused.

## What can close our Lean obligations

This table records the interfaces at arrival. The continuation results below
identify those now discharged, including the complete Published128 endpoint.

| Existing obligation or layer | Useful handoff input | Additional Lean work still needed |
|---|---|---|
| Sharp PROOF2 / 90-bit transfer | H's high/low joint methods offer alternatives | Round 7 already supplies the sharper theorem and transfer; preserve and audit them |
| P3 Lemma 3.1(d),(e), `PrimaryPHBound1123` | H §4's <164/q PH theorem implies the 1123 conclusion | Conditional PH distribution/rank proofs, trie soundness, 125 mixed rows, and literal block assembly; saved rows do not discharge these |
| F_r classes and 3125 assembly | No replacement needed | Existing lane already proves the ENH 3125/class layer; only the PH premise remains in `certified64_3125_of_ph` |
| Tag-only primary | H's weaker cube-root count | Existing round-7 sharp theorem is preferable |
| `SecondaryBlockBound729632` | H §9.1 mirrors the case split; fresh checksum equality event costs q^-2 | Complete unequal-count and tag-only cases, then use existing refined 604-mask lemmas |
| `SubcaseBBound` | H §8.3, pp.21–22, and `notes/04_joint/previous/partial_reduction_proof.md` | Already proved `rank_lemma64`; still connect two actual PH slices, shuffler compatibility, long masks, independent checksum weights, and N_h/S_h counts |
| `PHOneWordENHBound` | H §8.4 p.22 / earlier ENH notes: (2v+1)/q one-word high atom | Literal dyadic-bin count and PH/ENH/twist conditioning; the resulting 852²(2v+1)/q² is stronger than our requested threshold |
| Valuation-zero PH+ENH | H §8.5 p.23: 852²/q² | Use existing odd low-XOR bijection and shuffler elimination with actual independent coordinates |
| `TagOnlyBound` | H §8.7 p.25: 10359930880/q² | Actual tag mask support, high-product boundary count, then conditional checksum pattern bound; our stronger primary tag result can simplify this |
| Published128 assembly | H §3.1–3.4 pp.6–7, §9 pp.25–27 | Two-mode polynomial identities, common deterministic block witness, actual short/short joint count, averaging, one distinctness correction, and length arithmetic |
| Published64 assembly | H full-block/last-block split, §§6–7 pp.14–19 | Full-block <256/q; one fewer accepted root; complete concrete last-update analysis and encoding classifier |
| P4 Lemma 7.2 alternative | H Lemma 6.1 and 433-cell cover | Projection uniqueness for A,B,(A±B)/2; parity and nonzero-slope exceptions; outward polygon bounds, continuous coverage, lattice counts, multiplier-grid transfer |

The geometry has 288 off-line cells, 128 diagonal cells, 16 anti-diagonal
cells, and one intersection. Its largest saved bound is
18218787294413539421607/36893488147419103232 <494. The source's valid-
projection rules distinguish the actual parameter from the cell center;
crossing an exceptional line with a cell does not authorize a singular
projection for points on that line. `Certificates/Cells*.lean` proves only
saved rational comparisons, not these event inclusions or cover soundness
(H §10.2 p.28 and Appendix A pp.29–30; `lean/OBLIGATIONS.md` §E).

For the requested fingerprint headline, an even simpler dependency route
keeps P1's already accepted primary 364816/q. With the P5 secondary
729632/q and even the looser joint 2^-87, the first-bucket coefficient is
approximately 0.693: below 1. Thus neither `PrimaryPHBound1123` nor a 3125
theorem is a logical prerequisite for `Published128`. This does not close
the missing joint rows or justify the stronger 81/128 endpoint.

## Defect assessment and preservation

No counterexample to either requested endpoint, or to a P1–P5 collision
bound, was found in this comparison. Larger upper bounds in H do not
refute our smaller upper bounds. Both arguments agree on the single-
multiplier block-swap counterexample: x=256 zero bytes followed by 256
one bytes, y in reverse order, f=p-1. Updates commute modulo 8p, giving
probability at least 1/(p-2), which refutes the fingerprint headline for
that excluded sampler. The independent-multiplier model is unaffected
(H Remark 9.1 p.26; P5 Proposition 11.1).

One historical source wording error is recorded in [DEFECTS.md](DEFECTS.md):
the degree need not equal 2n. The consolidated paper already uses the
correct upper bound. It has no effect on either endpoint.

This comparison checks the mathematical reductions as written and the
specific geometry implementation. It does not certify every old large
computation, every uncompiled Lean proof body, or a full C refinement.
Unproved formal links remain obligations, not established defects.

## Vehicle decision

Use the existing ProvenHashes workspace, including the uncommitted round-7
work present on arrival. H has no accepted .olean artifacts, and its
`PrimaryAnalysis.full/last` and `FingerprintAnalysis.marginal0/marginal1/joint`
are still uninstantiated. Merely compiling `both_of_analyses` would not
advance these analytic obligations. Port useful arguments into the existing
literal model; do not switch toolchains or rebuild Mathlib.

## Results of the formalization continuation

The first import build exposed a missing final source file in our previous
round, rather than a mathematical defect: `UMASHPHENHSharp.lean` existed only
as a staging file. Its nine closure lemmas now compile, including both
90-bit corollaries and the exact sixty-case maximum. The fifteen ledger
certificates are retained unchanged.

The continuation also closes `SecondaryBlockBound729632`,
`DifferentChecksumsBound`, `TagOnlyBound`, `ClosedPHTwoWordENHBound`,
`OneWordENHBound`, and `ClosedTwoWordENHBound`. At the end of the first continuation the full joint-block
assembly required `SubcaseBBound` and `PHOneWordENHBound`. Round 2 has
now discharged both rows.

The short/short fingerprint event is now bounded by `1/q²` before OH
conditioning and `1/(q*(q-561))` afterwards, including overlapping short
noise indices. The product of independent root bounds is now averaged over
arbitrary finite OH data with both marginal identity probabilities and
the joint identity probability retained.

The proposed coarse-marginal shortcut is now an exact Lean arithmetic
certificate: using `364816/q`, `729632/q`, and a joint bound `2^-87`,
the first-bucket rounding coefficient is below `7/10`. Round 2 has now supplied the joint rows and all message identity reductions:
`published128 : Published128` compiles without an analytic premise.
Published64 remains open. Current signatures,
remaining propositions, audit evidence and commits are in [STATUS.md](STATUS.md).

## Round 2: the two-PH row is formally closed

`subcase_b_bound : SubcaseBBound` now proves the handoff's restricted
two-PH statement in the literal ProvenHashes model, with its original
constant `345763417/2^116`. The reference is H
`notes/04_joint/previous/partial_reduction_proof.md` §1.2–1.5.
The implemented proof uses §1.2's shuffler-difference elimination and a
different weighted census. For each secondary mask, the existing low and
high twisting weights are bounded by squares of rational numbers with
denominator 1024. The inequality `min(a,b) ≤ u*v` when `a ≤ u², b ≤ v²`
allows the lane sums to separate without a lane-independence assumption.

Three compatibility bits yield maximum weighted sums below 7500 and 5700.
For all shifts `3 ≤ h ≤ 15`, their product times `2^h` is at most
`1400832000000 < 1416246956032`. Shifts 1 and 2 use the certified total
weight bounds 47 and 38. The finite census enumerates only the previously
certified 852 reduction masks, never the key space. The statement permits
arbitrary other PH/ENH changes and tags and conditions on the twisting pair
only after the original pairs have been fixed.

This closes an obligation; it does not identify a defect in the handoff's
looser long-mask argument. This was the first of the two missing rows. The one-word row and the
complete joint block assembly have since been closed as described below.

## Round 2: the one-word row and the published fingerprint endpoint

The width-uniform one-word atom from H
`notes/04_joint/previous/earlier_enh_proof_notes.md`, §4, is now a theorem:
`one_word_high_count` bounds the count by `(2*v+1)*2^n` for arbitrary fixed
tags. Scaled coordinates, affine-XOR injectivity, and disjoint dyadic bins
are each checked separately. `enh_high_one_word_probability` transfers this
to the literal folded ENH and gives `127/q` at width 64.

For low valuations, the existing quadratic low-target proof already allows
a zero second divided increment. The new oriented interface exposes that
fact. A kernel-checked sum of the exact twisting weights is at most 6 on
the 248 even masks, sharpening the old popcount ceiling 10. Consequently,
the low ledger is at most `101418270720 < 2^37`. At valuations at least
four, the full PH atom and one-word ENH atom give
`852²*127/q² = 92189808/q²`. Together with valuation zero this proves
`ph_one_word_enh_bound : PHOneWordENHBound` with the unchanged `2^-91` target.
`joint_block_bound : JointBlockBound1416246956032` is unconditional.

The fingerprint composition now treats all message branches. Equal block
counts use one common distinguishing encoded position for both modes.
Unequal counts force both projections of the same leading block to zero.
The fresh twisting pair gives a secondary low fixed-target bound `297/q`,
so that joint zero event is bounded by `24354/q²`. Short/long polynomial
identities force both short constants to zero, with probability at most
`81/q²`; the two short noise indices are distinct. Short/short actual
collisions use the previously proved bound.

Averaging the two independent polynomial multipliers retains both marginal
identity events and their intersection, then conditions once on distinct OH
words. The existing coarse coefficient below `7/10` suffices for the exact
requested `published128 : Published128`. No stronger `81/128` coefficient
is claimed. This formalization found no new failed implication in H or P1–P5.
The primary headline still needs its separate sharp block and last-update
arguments; the finite geometric certificate alone does not provide them.

## Round 2: complete primary message assembly

`published64_of_primary_handoff` now proves the original Published64 target
from precisely `PrimaryFullBlockBound256` and `PrimaryLastUpdateBound503`.
The classifier, actual-prefix cancellation, excluded-zero root saving, OH
conditioning and ceiling arithmetic are checked. Unequal-count and short/long
headline branches are unconditional. The two remaining analytic propositions
are stated exactly in STATUS.md; full blocks use 256/q and the IID literal
last update uses 503/q before the one OH correction. This formalizes H §7's
assembly but does not assert the missing block estimates or assertion (14).
