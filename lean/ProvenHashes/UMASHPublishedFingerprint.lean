import ProvenHashes.UMASHFingerprintMessage
import ProvenHashes.UMASHFingerprintRounding

/-! The published two-multiplier fingerprint endpoint. Coarse compressor
marginals suffice, using the argument from the GPT-6 Pro handoff of
2026-09-19, Sections 3 and 9. Every compressor and identity premise has
been discharged for the literal reference construction. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] uniformProb wordFintype rootRate

theorem coarse_fingerprint_rate_le_published (L : ℕ) (hL : 1 ≤ L) :
    ((rootRate L)^2+rootRate L*((364816+729632:ℚ≥0)/q)+(1:ℚ≥0)/2^87)/
      (((q-561:ℕ):ℚ≥0)/q) ≤
      (((L+2^23-1)/2^23:ℕ):ℚ≥0)^2/(2:ℚ≥0)^83 := by
  let T : ℚ≥0 := ((L+2^23-1)/2^23:ℕ)
  have hT : 1 ≤ T := by
    dsimp only [T]
    exact_mod_cast fingerprint_bucket_positive L hL
  have hs := fingerprint_quadratic_scale (rootRate L) ((2:ℚ≥0)^19/(p-2:ℕ))
    ((364816+729632:ℚ≥0)/q) (1/2^87) T hT (rootRate_le_fingerprint_bucket L)
  have hcoef : coarseFingerprintRoundingK ≤ 1 :=
    fingerprint_coarse_rounding_certificate.1.le.trans fingerprint_coarse_rounding_certificate.2.le
  calc
    _ ≤ (T^2*(((2:ℚ≥0)^19/(p-2:ℕ))^2+((2:ℚ≥0)^19/(p-2:ℕ))*
        ((364816+729632:ℚ≥0)/q)+1/2^87))/(((q-561:ℕ):ℚ≥0)/q) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ = T^2*coarseFingerprintRoundingK/2^83 := by
      rw [mul_div_assoc,coarseFingerprintRoundingK_factor]
      ring
    _ ≤ T^2/2^83 := div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcoef (show (0:ℚ≥0) ≤ T^2 by positivity)) (by positivity)
-- CHECKPOINT

theorem published128 : Published128 := by
  intro L seed x y hL hx hy hne
  by_cases hshort : x.length ≤ 8 ∧ y.length ≤ 8
  · apply (short_fingerprint_distinct seed x y hshort.1 hshort.2 hne).trans
    have hT : (1:ℚ≥0) ≤ ((L+2^23-1)/2^23:ℕ) := by
      exact_mod_cast fingerprint_bucket_positive L hL
    have hT2 : (1:ℚ≥0) ≤ (((L+2^23-1)/2^23:ℕ):ℚ≥0)^2 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by positivity) hT 2
    exact (show (1:ℚ≥0)/(q*(q-561):ℕ) ≤ (1:ℚ≥0)/2^83 by apply NNRat.coe_le_coe.mp; norm_num [q]).trans
      (div_le_div_of_nonneg_right hT2 (by positivity))
  · exact (distinct_long_fingerprint_probability L seed x y hx hy hne (by omega)).trans
      (coarse_fingerprint_rate_le_published L hL)
-- CHECKPOINT

end ProvenHashes.UMASH
