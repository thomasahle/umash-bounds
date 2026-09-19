import ProvenHashes.UMASHRank

namespace ProvenHashes.UMASH
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem bitPolynomial_prefix_iff {w : ℕ} (a b : BitVec w) (j : ℕ) :
    a.toNat%2^j = b.toNat%2^j ↔
      ∀ i < j, (bitPolynomial a).coeff i = (bitPolynomial b).coeff i := by
  constructor
  · intro h i hi
    have he : a.setWidth j = b.setWidth j := BitVec.eq_of_toNat_eq
      (by simpa only [BitVec.toNat_setWidth] using h)
    have hb := congrArg (fun v : BitVec j => v.getLsbD i) he
    simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] at hb
    simpa only [coeff_bitPolynomial] using congrArg bitCoeff hb
  · intro h
    have he : a.setWidth j = b.setWidth j := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have hb := bitCoeff_injective (by simpa only [coeff_bitPolynomial] using h i hi)
      simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using hb
    simpa only [BitVec.toNat_setWidth] using congrArg BitVec.toNat he
-- CHECKPOINT

theorem clmul_preserves_prefix (d a b : Word) (j : ℕ)
    (h : a.toNat%2^j = b.toNat%2^j) :
    (clmul d a).toNat%2^j = (clmul d b).toNat%2^j := by
  have hp := (bitPolynomial_prefix_iff a b j).mp h
  apply (bitPolynomial_prefix_iff (clmul d a) (clmul d b) j).mpr
  intro i hi
  rw [bitPolynomial_clmul, bitPolynomial_clmul, Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro uv huv
  have he := Finset.mem_antidiagonal.mp huv
  rw [hp uv.2 (by omega)]
-- CHECKPOINT

theorem bitPolynomial_trailing_lt_of_prefix_ne {w : ℕ} (a : BitVec w) (j : ℕ)
    (hn : a.toNat%2^j ≠ 0) : (bitPolynomial a).natTrailingDegree < j := by
  by_contra hge
  have hp : ∀ i < j, (bitPolynomial a).coeff i = (bitPolynomial (0 : BitVec w)).coeff i := by
    intro i hi
    rw [bitPolynomial_zero, Polynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
  have hz := (bitPolynomial_prefix_iff a (0 : BitVec w) j).mpr hp
  exact hn (by simpa only [BitVec.toNat_zero, Nat.zero_mod] using hz)
-- CHECKPOINT

/-- An odd carry-less multiplier permits reconstruction of every input prefix. -/
theorem clmul_odd_reflects_prefix (d a b : Word) (hd : d.getLsbD 0 = true) (j : ℕ)
    (hout : (clmul d a).toNat%2^j = (clmul d b).toNat%2^j) :
    a.toNat%2^j = b.toNat%2^j := by
  by_contra hne
  let w := a ^^^ b
  have hwpre : w.toNat%2^j ≠ 0 := by
    dsimp only [w]
    rw [BitVec.toNat_xor, Nat.xor_mod_two_pow]
    intro hz
    have hh := congrArg (fun n => n ^^^ (b.toNat%2^j)) hz
    exact hne (by simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using hh)
  have hw : w ≠ 0 := by
    intro hz
    exact hwpre (by simp [hz])
  have hd0 : d ≠ 0 := by
    intro hz
    simp [hz] at hd
  have hdt : (bitPolynomial d).natTrailingDegree = 0 := by
    apply Polynomial.natTrailingDegree_eq_zero.mpr
    right
    rw [coeff_bitPolynomial, hd]
    norm_num [bitCoeff]
  have hwt := bitPolynomial_trailing_lt_of_prefix_ne w j hwpre
  have hz : (clmul d w).toNat%2^j = (0 : Wide).toNat%2^j := by
    dsimp only [w]
    rw [clmul_xor_right, BitVec.toNat_xor, Nat.xor_mod_two_pow, hout,
      Nat.xor_self]
    simp
  have hc := (bitPolynomial_prefix_iff (clmul d w) (0 : Wide) j).mp hz _ hwt
  rw [bitPolynomial_clmul, bitPolynomial_zero, Polynomial.coeff_zero] at hc
  have hprod : (bitPolynomial d*bitPolynomial w).coeff
      ((bitPolynomial d).natTrailingDegree+(bitPolynomial w).natTrailingDegree) ≠ 0 := by
    rw [Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]
    exact mul_ne_zero
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hd0))
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hw))
  rw [hdt, zero_add] at hprod
  exact hprod hc
-- CHECKPOINT

end ProvenHashes.UMASH
