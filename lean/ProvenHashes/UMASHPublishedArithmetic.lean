import ProvenHashes.UMASHContinuationObligations

namespace ProvenHashes.UMASH

def fingerprintMarginalSum : ℚ≥0 := (732757:ℚ≥0)/(q-561:ℕ)
def fingerprintJoint : ℚ≥0 := (1416246956032:ℚ≥0)/(q*(q-561):ℕ)
def fingerprintRoundingK : ℚ≥0 :=
  2^83*(fingerprintJoint+fingerprintMarginalSum*(2^19/(p-2:ℕ))+(2^19/(p-2:ℕ))^2)

/-- PROOF5 equation (8), certified exactly. This arithmetic theorem does not
assert the still-unproved message-level marginal or joint collision bounds. -/
theorem fingerprint_rounding_certificate :
    fingerprintRoundingK =
      (61555182062916914709644342474504392009252905535823413248:ℚ≥0)/
        98079714615416883696934812005564729285413570653510954055 ∧
    fingerprintRoundingK < (81:ℚ≥0)/128 ∧ (81:ℚ≥0)/128 < 1 := by
  norm_num [fingerprintRoundingK, fingerprintMarginalSum, fingerprintJoint, p, q]
-- CHECKPOINT

/-- PROOF4 equation (25), including both distinct-key denominators. -/
theorem headline_rounding_certificate :
    (57:ℚ≥0) < 2^61*(headlineA+32/(p-2:ℕ)) ∧
    2^61*(headlineA+32/(p-2:ℕ)) < (58:ℚ≥0) ∧
    (56:ℚ≥0) < 2^61*headlineS ∧ 2^61*headlineS < (57:ℚ≥0) := by
  norm_num [headlineA, headlineS, p, q]
-- CHECKPOINT

/-- PROOF4's proposed envelope implies the strict coefficient 58 at every
positive length. Establishing that envelope for collisions is a separate target. -/
theorem headlineEnvelope_lt_linear (L : ℕ) (hL : 1 ≤ L) :
    headlineEnvelope L < 58*(((L+511)/512:ℕ):ℚ≥0)/2^61 := by
  by_cases h : L = 1
  · subst L
    norm_num [headlineEnvelope, q]
  have hceil : (L+31)/32 ≤ 16*((L+511)/512) := by omega
  have hceilQ : (((L+31)/32:ℕ):ℚ) ≤ 16*(((L+511)/512:ℕ):ℚ) := by
    exact_mod_cast hceil
  have hpos : (1:ℚ) ≤ (((L+511)/512:ℕ):ℚ) := by
    exact_mod_cast (show 1 ≤ (L+511)/512 by omega)
  have hr : rootRate L ≤ 2*((((L+31)/32:ℕ):ℚ≥0))/(p-2:ℕ) := min_le_right _ _
  have hrQ := NNRat.coe_le_coe.mpr hr
  have hcomp : ((1-headlineA:ℚ≥0):ℚ) = 1-(headlineA:ℚ) := by
    rw [NNRat.coe_sub (by apply NNRat.coe_le_coe.mp; norm_num [headlineA, q] : headlineA ≤ 1)]
    rfl
  apply NNRat.coe_lt_coe.mp
  simp only [headlineEnvelope, h, ite_false, NNRat.coe_max,
    NNRat.coe_add, NNRat.coe_mul, hcomp]
  norm_num [headlineA, headlineS, p, q] at hrQ ⊢
  constructor <;> nlinarith
-- CHECKPOINT

end ProvenHashes.UMASH
