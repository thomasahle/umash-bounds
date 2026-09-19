import ProvenHashes.UMASHPolynomial
import ProvenHashes.UMASHJointProbability

namespace ProvenHashes.UMASH
open scoped Classical

/-- A nonzero comparison polynomial on the exact reference multiplier range. -/
theorem polynomial_key_root_probability (P : Polynomial Field) (hP : P ≠ 0) :
    uniformProb (fun f : PolyKey => P.eval (f.val.val : Field) = 0) ≤
      (P.natDegree : ℚ≥0)/(p-2:ℕ) := by
  classical
  have hc := Classic.restricted_roots (fun f : PolyKey => (f.val.val : Field))
    polyKey_field_injective P hP
  unfold uniformProb
  rw [polyKey_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  convert hc using 2 <;> ext f <;> simp [Polynomial.IsRoot]
-- CHECKPOINT

/-- The identity event contributes one; every other polynomial uses the
clipped root bound on the independent multiplier. -/
theorem polynomial_key_root_rate (P : Polynomial Field) (d : ℕ) (hd : P.natDegree ≤ d) :
    uniformProb (fun f : PolyKey => P.eval (f.val.val : Field) = 0) ≤
      if P = 0 then 1 else min 1 ((d:ℚ≥0)/(p-2:ℕ)) := by
  split_ifs with hP
  · exact probability_le_one _
  · apply le_min (probability_le_one _)
    exact (polynomial_key_root_probability P hP).trans
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr hd) (by positivity))
-- CHECKPOINT

/-- The pointwise two-multiplier part of PROOF5 Lemma 7.1. The polynomials
are fixed here (as after conditioning on all OH words); only the multiplier
coordinates are independent. Either comparison polynomial may be zero. -/
theorem independent_polynomial_root_product (P0 P1 : Polynomial Field) (d : ℕ)
    (h0 : P0.natDegree ≤ d) (h1 : P1.natDegree ≤ d) :
    uniformProb (fun f : PolyKey × PolyKey =>
      P0.eval (f.1.val.val : Field) = 0 ∧ P1.eval (f.2.val.val : Field) = 0) ≤
      (if P0 = 0 then 1 else min 1 ((d:ℚ≥0)/(p-2:ℕ))) *
      (if P1 = 0 then 1 else min 1 ((d:ℚ≥0)/(p-2:ℕ))) := by
  have hP0 := polynomial_key_root_rate P0 d h0
  have hP1 := polynomial_key_root_rate P1 d h1
  have hp := probability_and_prod_le
    (fun f : PolyKey => P0.eval (f.val.val : Field) = 0)
    (fun f : PolyKey × PolyKey => P1.eval (f.2.val.val : Field) = 0)
    (if P1 = 0 then 1 else min 1 ((d:ℚ≥0)/(p-2:ℕ))) (fun _ => hP1)
  exact hp.trans (mul_le_mul_of_nonneg_right hP0 (by positivity))
-- CHECKPOINT

end ProvenHashes.UMASH
