import ProvenHashes.UMASHShufflerInverse
import ProvenHashes.UMASHTwistWeights
import ProvenHashes.UMASHLowTargetQuadratic

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet

/-- The separate PH difference fixed by two raw compressor masks, PROOF2 (7). -/
def phenhPHMask (s u v : ℕ) : Word :=
  phShuffleInverse s (BitVec.ofNat 64 u ^^^ BitVec.ofNat 64 v)

/-- The corresponding separate ENH difference. -/
def phenhENHMask (s u v : ℕ) : ℕ :=
  (BitVec.ofNat 64 u ^^^ phenhPHMask s u v).toNat

/-- The exact low-lane sum in PROOF2 (21). -/
def phenhLowLedger (r s : ℕ) : ℚ≥0 :=
  2^r * ∑ u ∈ valuationMasks r, ∑ v ∈ valuationMasks r,
    lowTargetK r (phenhENHMask s u v)*twistLowWeight v

/-- The exact high-lane sum in PROOF2 (22); a full carryless product has no
bit at position 127, hence the explicit high-PH top-bit filter. -/
def phenhHighLedger (s : ℕ) : ℚ≥0 :=
  ∑ u ∈ maskSet, ∑ v ∈ maskSet,
    if (phenhPHMask s u v).toNat < 2^63 then
      highTargetK (phenhENHMask s u v)*twistHighWeight v else 0

/-- The remaining literal-block assembly for PROOF2 Lemma 6.1.
This is a definition of a proposition, not a postulated bound. -/
def PHENHJointLedgerReduction : Prop := ∀ (seed : Word) (x y : Block),
  x.Valid → y.Valid → sameCount x y → dataChecksum x = dataChecksum y →
  phDiffCount x y = 1 → enhChanges x y = 2 →
  1 ≤ enhValuation x y → enhValuation x y ≤ 63 →
  ∃ s : ℕ, 1 ≤ s ∧ s ≤ 15 ∧
    uniformProb (jointEvent seed x y) ≤
      (if enhValuation x y < 4 then phenhLowLedger (enhValuation x y) s
        else phenhHighLedger s)/q^2

/-- The sixty exact finite-sum bounds, still requiring kernel certificates. -/
def PHENHJointLedgerCertificate : Prop :=
  (∀ r s : ℕ, 1 ≤ r → r ≤ 3 → 1 ≤ s → s ≤ 15 → phenhLowLedger r s ≤ 170906186782) ∧
  (∀ s : ℕ, 1 ≤ s → s ≤ 15 → phenhHighLedger s ≤ 170906186782)

/-- The sharp joint conclusion follows from exactly the remaining block
reduction and sixty finite certificates; both premises remain explicit. -/
theorem joint_phenh_sharp_of_ledger (hred : PHENHJointLedgerReduction)
    (hcert : PHENHJointLedgerCertificate) : JointPHENHSharpBound := by
  intro seed x y hx hy hc hs hp he hr hr'
  obtain ⟨s, hs1, hs15, hb⟩ := hred seed x y hx hy hc hs hp he hr hr'
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs with hv
  · exact hcert.1 (enhValuation x y) s hr (by omega) hs1 hs15
  · exact hcert.2 s hs1 hs15
-- CHECKPOINT

end ProvenHashes.UMASH
