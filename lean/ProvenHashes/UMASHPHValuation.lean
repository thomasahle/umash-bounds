import ProvenHashes.UMASHPHPrefix
import ProvenHashes.UMASHENHPrimary

namespace ProvenHashes.UMASH
open Polynomial
set_option maxHeartbeats 2000000

theorem bitPolynomial_prefix_zero_of_le {w : ℕ} (x : BitVec w) (j : ℕ)
    (hj : j ≤ (bitPolynomial x).natTrailingDegree) : x.toNat%2^j = 0 := by
  have h : x.toNat%2^j = (0 : BitVec w).toNat%2^j := by
    apply (bitPolynomial_prefix_iff x (0 : BitVec w) j).mpr
    intro i hi
    rw [bitPolynomial_zero, Polynomial.coeff_zero]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
  simpa only [BitVec.toNat_zero, Nat.zero_mod] using h
-- CHECKPOINT

theorem bitPolynomial_trailing_eq_padic (d : Word) (hd : d ≠ 0) :
    (bitPolynomial d).natTrailingDegree = padicValNat 2 d.toNat := by
  have hn : d.toNat ≠ 0 := by
    intro h
    exact hd (BitVec.eq_of_toNat_eq (by simpa using h))
  have hpre := bitPolynomial_prefix_zero_of_le d (bitPolynomial d).natTrailingDegree le_rfl
  have hle : (bitPolynomial d).natTrailingDegree ≤ padicValNat 2 d.toNat :=
    (padicValNat_dvd_iff_le hn).mp (Nat.dvd_of_mod_eq_zero hpre)
  apply Nat.le_antisymm hle
  by_contra hlt
  have hzero : d.toNat%2^(padicValNat 2 d.toNat) = 0 := Nat.mod_eq_zero_of_dvd pow_padicValNat_dvd
  have hc := (bitPolynomial_prefix_iff d (0 : Word) (padicValNat 2 d.toNat)).mp
    (by simpa only [BitVec.toNat_zero, Nat.zero_mod] using hzero)
    (bitPolynomial d).natTrailingDegree (by omega)
  rw [bitPolynomial_zero, Polynomial.coeff_zero, coeff_bitPolynomial,
    (bitPolynomial_trailing d hd).2] at hc
  norm_num [bitCoeff] at hc
-- CHECKPOINT

theorem clmul_low_divisible (d k : Word) (r : ℕ) (hr : r ≤ 64)
    (hd : 2^r ∣ d.toNat) : 2^r ∣ (split (clmul d k)).1.toNat := by
  have hz : clmul k (0 : Word) = 0 := by
    apply bitPolynomial_injective
    rw [bitPolynomial_clmul, bitPolynomial_zero, mul_zero, bitPolynomial_zero]
  have hp := clmul_preserves_prefix k d (0 : Word) r
    (by simpa only [BitVec.toNat_zero, Nat.zero_mod] using Nat.mod_eq_zero_of_dvd hd)
  rw [clmul_comm k d, hz] at hp
  apply Nat.dvd_of_mod_eq_zero
  simpa only [split, BitVec.toNat_setWidth,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hr), BitVec.toNat_zero, Nat.zero_mod] using hp
-- CHECKPOINT

/-- A truncated product determines the first 64-r key bits, where r is the
first nonzero coefficient of the multiplier. -/
theorem clmul_low_reflects_prefix (d a b : Word) (hd : d ≠ 0)
    (r : ℕ) (hr : r = (bitPolynomial d).natTrailingDegree)
    (hout : (split (clmul d a)).1 = (split (clmul d b)).1) :
    a.toNat%2^(64-r) = b.toNat%2^(64-r) := by
  by_contra hne
  let w := a ^^^ b
  have hwpre : w.toNat%2^(64-r) ≠ 0 := by
    dsimp only [w]
    rw [BitVec.toNat_xor, Nat.xor_mod_two_pow]
    intro hz
    have hh := congrArg (fun n => n ^^^ (b.toNat%2^(64-r))) hz
    exact hne (by simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using hh)
  have hw : w ≠ 0 := by intro hz; exact hwpre (by simp [hz])
  have hwt := bitPolynomial_trailing_lt_of_prefix_ne w (64-r) hwpre
  have hdr : r < 64 := hr ▸ (bitPolynomial_trailing d hd).1
  have hi : (bitPolynomial d).natTrailingDegree+(bitPolynomial w).natTrailingDegree < 64 := by
    omega
  have he : (clmul d a).toNat%2^64 = (clmul d b).toNat%2^64 := by
    simpa only [split, BitVec.toNat_setWidth] using congrArg BitVec.toNat hout
  have hz : (clmul d w).toNat%2^64 = (0 : Wide).toNat%2^64 := by
    dsimp only [w]
    rw [clmul_xor_right, BitVec.toNat_xor, Nat.xor_mod_two_pow, he, Nat.xor_self]
    simp
  have hc := (bitPolynomial_prefix_iff (clmul d w) (0 : Wide) 64).mp hz _ hi
  rw [bitPolynomial_clmul, bitPolynomial_zero, Polynomial.coeff_zero,
    Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree] at hc
  exact (mul_ne_zero
    (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hd))
    (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hw))) hc
-- CHECKPOINT

end ProvenHashes.UMASH
