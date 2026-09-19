# Continuation of 2026-09-19

The authoritative endpoint status and exact remaining propositions are in
`STATUS.md`. The development remains PARTIAL. The vehicle is the existing
Lean 4.24 workspace; the handoff's 4.19 project was not provisioned.

## Accepted work

This continuation adds 37 theorem declarations in eleven modules and
compiles the nine previously staged `UMASHPHENHSharp` closure lemmas.
The complete source tree contains 1444 audited theorem/lemma declarations.
All existing source modules, including the uncommitted round-7 certificates,
are preserved. `check-handoff.py` checks the arrival source hashes from the
first new checkpoint, in addition to the baseline preservation checker.

- `UMASHDifferentChecksums`: the retained-primary product bound over the
  twisting pair and the stronger joint `364816^2/q^2` estimate.
- `UMASHSecondaryTag`: key-dependent common XOR masks are permitted in the
  pointwise tag-boundary inclusion. This proves the secondary tag marginal.
- `UMASHSecondaryLengths`: unequal-count checksums coincide with probability
  at most `q^-2`; partition by that event before exposing the twisting pair.
- `UMASHSecondaryBlock`: unconditional `SecondaryBlockBound729632`.
- `UMASHJointTag`: a prefix-popcount gap bounds the high twisting numerator
  for 54-bit tag masks; retained-primary conditioning closes `TagOnlyBound`.
- `UMASHPHENHZero`: uniform low PH and ENH targets, combined through the
  existing exact shuffler inverse, close the valuation-zero row. Together
  with sharp PROOF2 this gives `ClosedPHTwoWordENHBound`.
- `UMASHJointLengths`: unequal-count joint estimate `29914913/q^2`, and
  named closures of both ENH-only obligation rows.
- `UMASHJointBlock`: exhaustive assembly with exactly `SubcaseBBound` and
  `PHOneWordENHBound` as premises. It is not an unconditional joint bound.
- `UMASHJointMixture`: arbitrary finite averaging of the two independent
  polynomial root estimates, retaining both identity marginals and their
  joint event.
- `UMASHShortFingerprint`: short/short fingerprints, including overlapping
  noise indices. Expose the larger length plus four, which is absent from
  the primary event. The distinct-key result is `1/(q*(q-561))`.
- `UMASHCoarseArithmetic`: using the accepted coarse marginals, even a joint
  block bound of `2^-87` leaves the headline coefficient below `7/10`.

The final sharp-ledger maximum required making the large ledger functions
locally irreducible before reducing the attaining case. The generator and
its staging source contain the same repair. No certificate value changed.

## Next analytic work

1. `SubcaseBBound`: two PH slices, the difference of two shufflers, retained
   low-bit compatibility, long masks, and the N_h/S_h finite census. The
   shifted-product rank theorem is already available in `UMASHRank`.
2. `PHOneWordENHBound`: the handoff's dyadic-bin high atom `(2v+1)/q` is a
   useful simplification. Prove the literal one-word ENH atom, then combine
   it with the independent PH slice and the common-checksum twisting pair.
3. For Published128, lift block identities to a common deterministic
   distinguishing block in both polynomial modes. Complete long/long and
   short/long comparisons; short/short is now closed. Then apply the proved
   averaged root estimate, condition OH once, and round lengths.
4. For Published64, the stronger PH/common-PH estimates and complete literal
   last-update analysis remain. The 433 saved geometric cell bounds alone
   do not establish their coverage or probability-event soundness.
5. For the stronger 3125 route, PROOF3 parts (d),(e), convolution and the PH
   valuation assembly remain. The tag, ENH and F_r layers are already closed.

## Reproduction and editing

Use `bash reproduce-handoff.sh`, with the parent Mathlib cache present.
The script uses CPU 0-31, sixteen Lean threads, and nice level 10. It restores
the checkpoint-log archive when supplied. Every theorem was compiled after
its addition using `build-handoff.sh` and `stage-handoff.py`; the stage start
argument is the number of already checked checkpoint segments.

Do not infer endpoint closure from the axiom audit: conditional theorems
also have only standard axioms. Read their explicit signatures.

The `probability_scaled_indicator` helper accepts a `DecidablePred` instance
and proves the equality between its filter and the classical filter used
by `uniformProb`. This avoids definitional-equality failures when a compound
predicate has a different synthesized decision procedure. The polynomial
averaging corollary similarly normalizes the two identity cases explicitly.
