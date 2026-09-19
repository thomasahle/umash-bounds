import ProvenHashes.UMASHModel

/-! The literal carry-less multiplication loop as multiplication in GF(2)[X].
All bit-vector identities below are proved from their bit semantics. -/
namespace ProvenHashes.UMASH

open Polynomial
open scoped BigOperators

def bitCoeff (b : Bool) : ZMod 2 := if b then 1 else 0

noncomputable def bitPolynomial {w : ℕ} (x : BitVec w) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range w, monomial i (bitCoeff (x.getLsbD i))

theorem bitCoeff_injective : Function.Injective bitCoeff := by
  intro a b h
  cases a <;> cases b <;> norm_num [bitCoeff] at *
-- CHECKPOINT

theorem bitCoeff_xor (a b : Bool) : bitCoeff (a ^^ b) = bitCoeff a + bitCoeff b := by
  cases a <;> cases b <;> decide
-- CHECKPOINT

theorem coeff_bitPolynomial {w : ℕ} (x : BitVec w) (i : ℕ) :
    (bitPolynomial x).coeff i = bitCoeff (x.getLsbD i) := by
  classical
  by_cases hi : i < w
  · simp [bitPolynomial, Polynomial.coeff_sum, Polynomial.coeff_monomial, hi]
  · simp [bitPolynomial, Polynomial.coeff_sum, Polynomial.coeff_monomial, hi,
      BitVec.getLsbD_of_ge x i (by omega), bitCoeff]
-- CHECKPOINT

theorem bitPolynomial_injective {w : ℕ} :
    Function.Injective (bitPolynomial : BitVec w → Polynomial (ZMod 2)) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  apply bitCoeff_injective
  simpa only [coeff_bitPolynomial] using congrArg (fun p => p.coeff i) h
-- CHECKPOINT

@[simp] theorem bitPolynomial_zero (w : ℕ) : bitPolynomial (0 : BitVec w) = 0 := by
  ext i
  simp [coeff_bitPolynomial, bitCoeff]
-- CHECKPOINT

theorem bitPolynomial_xor {w : ℕ} (x y : BitVec w) :
    bitPolynomial (x ^^^ y) = bitPolynomial x + bitPolynomial y := by
  ext i
  simp only [coeff_bitPolynomial, Polynomial.coeff_add, BitVec.getLsbD_xor, bitCoeff_xor]
-- CHECKPOINT

/-- A zero-extended left shift is an exact polynomial shift when it fits. -/
theorem bitPolynomial_shift {w n s : ℕ} (x : BitVec w) (h : w+s ≤ n) :
    bitPolynomial (x.zeroExtend n <<< s) = X^s * bitPolynomial x := by
  ext i
  rw [coeff_bitPolynomial, Polynomial.coeff_X_pow_mul']
  simp only [coeff_bitPolynomial, BitVec.zeroExtend, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  by_cases hs : s ≤ i
  · by_cases hi : i < n
    · simp [hs, hi, show ¬ i < s by omega, show i-s < n by omega]
    · simp [hs, hi, BitVec.getLsbD_of_ge x (i-s) (by omega), bitCoeff]
  · simp [hs, show i < s by omega, bitCoeff]
-- CHECKPOINT

theorem bitPolynomial_xor_fold {w : ℕ} {A : Type*} (l : List A)
    (f : A → BitVec w) (a : BitVec w) :
    bitPolynomial (l.foldl (fun acc i => acc ^^^ f i) a) =
      bitPolynomial a + (l.map (fun i => bitPolynomial (f i))).sum := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, ih, bitPolynomial_xor, List.map_cons, List.sum_cons]
    exact add_assoc _ _ _
-- CHECKPOINT

/-- The reference loop computes the unreduced binary-polynomial product. -/
theorem bitPolynomial_clmul (a b : Word) :
    bitPolynomial (clmul a b) = bitPolynomial a * bitPolynomial b := by
  classical
  calc
    bitPolynomial (clmul a b) = ∑ i ∈ Finset.range 64,
        bitPolynomial (if a.getLsbD i then b.zeroExtend 128 <<< i else 0) := by
      rw [clmul, bitPolynomial_xor_fold, bitPolynomial_zero, zero_add]
      symm
      simpa using List.sum_toFinset
        (fun i => bitPolynomial (if a.getLsbD i then b.zeroExtend 128 <<< i else 0))
        (List.nodup_range (n := 64))
    _ = (∑ i ∈ Finset.range 64, monomial i (bitCoeff (a.getLsbD i))) *
        bitPolynomial b := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : 64+i ≤ 128 := by have := Finset.mem_range.mp hi; omega
      cases ha : a.getLsbD i
      · simpa [bitCoeff] using (bitPolynomial_zero 128)
      · simpa [bitCoeff, ← C_mul_X_pow_eq_monomial] using bitPolynomial_shift b hi'
    _ = bitPolynomial a * bitPolynomial b := rfl
-- CHECKPOINT

theorem bitPolynomial_ne_zero {w : ℕ} {x : BitVec w} (h : x ≠ 0) :
    bitPolynomial x ≠ 0 := by
  intro hx
  apply h
  apply bitPolynomial_injective
  exact hx.trans (bitPolynomial_zero w).symm
-- CHECKPOINT

theorem clmul_left_injective {d : Word} (hd : d ≠ 0) :
    Function.Injective (clmul d) := by
  intro x y h
  apply bitPolynomial_injective
  apply mul_left_cancel₀ (bitPolynomial_ne_zero hd)
  simpa only [bitPolynomial_clmul] using congrArg bitPolynomial h
-- CHECKPOINT

theorem clmul_comm (x y : Word) : clmul x y = clmul y x := by
  apply bitPolynomial_injective
  simp only [bitPolynomial_clmul, mul_comm]
-- CHECKPOINT

theorem clmul_xor_left (x y z : Word) :
    clmul (x ^^^ y) z = clmul x z ^^^ clmul y z := by
  apply bitPolynomial_injective
  simp only [bitPolynomial_clmul, bitPolynomial_xor, add_mul]
-- CHECKPOINT

theorem clmul_xor_right (x y z : Word) :
    clmul x (y ^^^ z) = clmul x y ^^^ clmul x z := by
  apply bitPolynomial_injective
  simp only [bitPolynomial_clmul, bitPolynomial_xor, mul_add]
-- CHECKPOINT

end ProvenHashes.UMASH
