import ProvenHashes.UMASHLongJointIdentities
import ProvenHashes.UMASHShortConstants

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem message_secondary_identity_probability (seed : Word) (x y : Message)
    (hne : x ≠ y) (hlong : 8 < x.length ∨ 8 < y.length) :
    uniformProb (fun k : OHKey => modePolynomial true k seed x = modePolynomial true k seed y) ≤
      (729632:ℚ≥0)/q := by
  by_cases hx : 8 < x.length
  · by_cases hy : 8 < y.length
    · exact long_secondary_identity_probability seed x y hx hy hne
    · have h := (mode_short_long_identity_probability true seed y x (by omega) hx).trans
        (by apply NNRat.coe_le_coe.mp; norm_num [q] : (9:ℚ≥0)/q ≤ 729632/q)
      simpa only [eq_comm] using h
  · exact (mode_short_long_identity_probability true seed x y (by omega) (hlong.resolve_left hx)).trans
      (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

theorem message_joint_identity_probability (seed : Word) (x y : Message)
    (hne : x ≠ y) (hlong : 8 < x.length ∨ 8 < y.length) :
    uniformProb (fun k : OHKey =>
      modePolynomial false k seed x = modePolynomial false k seed y ∧
      modePolynomial true k seed x = modePolynomial true k seed y) ≤ (1416246956032:ℚ≥0)/q^2 := by
  by_cases hx : 8 < x.length
  · by_cases hy : 8 < y.length
    · exact long_joint_identity_probability seed x y hx hy hne
    · have h := (short_long_joint_identity_probability seed y x (by omega) hx).trans
        (by apply NNRat.coe_le_coe.mp; norm_num [q] : (81:ℚ≥0)/q^2 ≤ 1416246956032/q^2)
      simpa only [eq_comm] using h
  · exact (short_long_joint_identity_probability seed x y (by omega) (hlong.resolve_left hx)).trans
      (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
