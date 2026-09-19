import ProvenHashes.UMASHCoarseArithmetic

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] rootRate

theorem fingerprint_bucket_positive (L : ℕ) (hL : 1 ≤ L) :
    1 ≤ (L+2^23-1)/2^23 := by omega
-- CHECKPOINT

theorem rootRate_le_fingerprint_bucket (L : ℕ) :
    rootRate L ≤ ((2:ℚ≥0)^19/(p-2:ℕ))*((L+2^23-1)/2^23:ℕ) := by
  rw [rootRate]
  apply (min_le_right _ _).trans
  have hceil : 2*((L+31)/32) ≤ 2^19*((L+2^23-1)/2^23) := by omega
  calc
    _ ≤ ((2:ℚ≥0)^19*((L+2^23-1)/2^23:ℕ))/(p-2:ℕ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hceil
    _ = _ := by ring
-- CHECKPOINT

theorem fingerprint_quadratic_scale (r c m j T : ℚ≥0) (hT : 1 ≤ T) (hr : r ≤ c*T) :
    r^2+r*m+j ≤ T^2*(c^2+c*m+j) := by
  have hT2 : T ≤ T^2 := by
    simpa only [one_mul,pow_two] using mul_le_mul_of_nonneg_right hT (show (0:ℚ≥0) ≤ T by positivity)
  have h1T2 : 1 ≤ T^2 := hT.trans hT2
  have hsq : r^2 ≤ T^2*c^2 :=
    (pow_le_pow_left₀ (by positivity) hr 2).trans_eq (by ring)
  have hlin : r*m ≤ T^2*(c*m) := by
    calc
      _ ≤ c*T*m := mul_le_mul_of_nonneg_right hr (by positivity)
      _ ≤ c*T^2*m := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hT2 (by positivity)) (by positivity)
      _ = _ := by ring
  have hconst : j ≤ T^2*j := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h1T2 (show (0:ℚ≥0) ≤ j by positivity)
  exact (add_le_add (add_le_add hsq hlin) hconst).trans_eq (by ring)
-- CHECKPOINT

theorem coarseFingerprintRoundingK_factor :
    (((2:ℚ≥0)^19/(p-2:ℕ))^2+((2:ℚ≥0)^19/(p-2:ℕ))*((364816+729632:ℚ≥0)/q)+1/2^87)/
      (((q-561:ℕ):ℚ≥0)/q) = coarseFingerprintRoundingK/2^83 := by
  norm_num [coarseFingerprintRoundingK,p,q]
-- CHECKPOINT

end ProvenHashes.UMASH
