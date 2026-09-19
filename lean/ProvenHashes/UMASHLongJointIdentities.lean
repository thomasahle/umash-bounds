import ProvenHashes.UMASHModePolynomial
import ProvenHashes.UMASHBlockZeroTargets
import ProvenHashes.UMASHJointBlockComplete
import ProvenHashes.UMASHSecondaryBlock

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem long_secondary_identity_probability (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hne : x ≠ y) :
    uniformProb (fun k : OHKey => modePolynomial true k seed x = modePolynomial true k seed y) ≤
      (729632:ℚ≥0)/q := by
  have ordered (a b : Message) (ha : 8 < a.length) (hb : 8 < b.length)
      (hc : (encode a).length < (encode b).length) :
      uniformProb (fun k : OHKey => modePolynomial true k seed a = modePolynomial true k seed b) ≤
        (729632:ℚ≥0)/q := by
    obtain ⟨bb,hbb,hw⟩ := mode_different_count_witness seed a b ha hb hc
    exact ((probability_mono (fun k hk => hw true k hk)).trans
      (secondary_zero_probability seed bb hbb)).trans
        (by apply NNRat.coe_le_coe.mp; norm_num [q])
  rcases lt_trichotomy (encode x).length (encode y).length with hc | hc | hc
  · exact ordered x y hx hy hc
  · obtain ⟨bx,byy,hvx,hvy,ht,hw⟩ := mode_same_count_witness seed x y hx hy hne hc
    exact (probability_mono (fun k hk => hw true k hk)).trans
      (secondary_block_bound seed bx byy hvx hvy ht)
  · simpa only [eq_comm] using ordered y x hy hx hc
-- CHECKPOINT

theorem long_joint_identity_probability (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hne : x ≠ y) :
    uniformProb (fun k : OHKey =>
      modePolynomial false k seed x = modePolynomial false k seed y ∧
      modePolynomial true k seed x = modePolynomial true k seed y) ≤ (1416246956032:ℚ≥0)/q^2 := by
  have ordered (a b : Message) (ha : 8 < a.length) (hb : 8 < b.length)
      (hc : (encode a).length < (encode b).length) :
      uniformProb (fun k : OHKey =>
        modePolynomial false k seed a = modePolynomial false k seed b ∧
        modePolynomial true k seed a = modePolynomial true k seed b) ≤ (1416246956032:ℚ≥0)/q^2 := by
    obtain ⟨bb,hbb,hw⟩ := mode_different_count_witness seed a b ha hb hc
    exact ((probability_mono (fun k hk => And.intro (hw false k hk.1) (hw true k hk.2))).trans
      (joint_zero_probability seed bb hbb)).trans
        (by apply NNRat.coe_le_coe.mp; norm_num [q])
  rcases lt_trichotomy (encode x).length (encode y).length with hc | hc | hc
  · exact ordered x y hx hy hc
  · obtain ⟨bx,byy,hvx,hvy,ht,hw⟩ := mode_same_count_witness seed x y hx hy hne hc
    exact (probability_mono (fun k hk => And.intro (hw false k hk.1) (hw true k hk.2))).trans
      (joint_block_bound seed bx byy hvx hvy ht)
  · simpa only [eq_comm] using ordered y x hy hx hc
-- CHECKPOINT

end ProvenHashes.UMASH
