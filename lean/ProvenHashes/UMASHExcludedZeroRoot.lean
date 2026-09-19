import ProvenHashes.UMASHIndependentRoots
import ProvenHashes.UMASHModePolynomial

/-! Excluded-zero root saving for the argument from the GPT-6 Pro handoff of 2026-09-19, Section 7. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

/-- Long-message comparison polynomials have an excluded zero root. Removing
X saves one accepted root on the actual multiplier set {2,...,p-1}. -/
theorem polynomial_key_root_probability_zero_constant (P : Polynomial Field)
    (hP : P ≠ 0) (h0 : P.coeff 0 = 0) :
    uniformProb (fun f : PolyKey => P.eval (f.val.val:Field) = 0) ≤
      ((P.natDegree-1:ℕ):ℚ≥0)/(p-2:ℕ) := by
  have hf : P = Polynomial.X*P.divX := by
    simpa only [h0,Polynomial.C_0,add_zero] using (Polynomial.X_mul_divX_add P).symm
  have hdiv : P.divX ≠ 0 := by
    intro hz
    exact hP (by rw [hf,hz,mul_zero])
  have hm : uniformProb (fun f : PolyKey => P.eval (f.val.val:Field) = 0) ≤
      uniformProb (fun f : PolyKey => P.divX.eval (f.val.val:Field) = 0) := by
    apply probability_mono
    intro f h
    have hn : (f.val.val:Field) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      simp only [ZMod.val_natCast,ZMod.val_zero,Nat.mod_eq_of_lt f.val.isLt] at hv
      have := f.property
      omega
    rw [hf,Polynomial.eval_mul,Polynomial.eval_X] at h
    exact (mul_eq_zero.mp h).resolve_left hn
  exact (hm.trans (polynomial_key_root_probability P.divX hdiv)).trans_eq
    (by rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one])
-- CHECKPOINT

/-- The difference of the two long streams retains its zero constant term,
including when leading coefficients vanish. -/
theorem long_mode_difference_constant_zero (mode : Bool) (k : OHKey) (seed : Word)
    (x y : Message) (hx : 8 < x.length) (hy : 8 < y.length) :
    (modePolynomial mode k seed x-modePolynomial mode k seed y).coeff 0 = 0 := by
  simp only [Polynomial.coeff_sub,modePolynomial,if_neg (by omega : ¬x.length ≤ 8),
    if_neg (by omega : ¬y.length ≤ 8),blockPolynomial_constant,sub_self]
-- CHECKPOINT

end ProvenHashes.UMASH
