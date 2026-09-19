import ProvenHashes.UMASHSinglePH

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

/-- Equality of low input bits is equivalent to divisibility of the wrapped
additive difference. This uses the actual word subtraction modulo 2^64. -/
theorem word_prefix_eq_iff_sub_dvd (x y : Word) (r : ℕ) (hr : r ≤ 64) :
    x.toNat%2^r = y.toNat%2^r ↔ 2^r ∣ (y-x).toNat := by
  have hadd : (y-x).setWidth r + x.setWidth r = y.setWidth r := by
    rw [← BitVec.setWidth_add _ _ hr, sub_add_cancel]
  constructor
  · intro h
    have he : x.setWidth r = y.setWidth r := BitVec.eq_of_toNat_eq (by simpa using h)
    have hz : (y-x).setWidth r = 0 := by
      apply add_right_cancel (b := x.setWidth r)
      simpa only [zero_add, he] using hadd
    apply Nat.dvd_of_mod_eq_zero
    have ht := congrArg BitVec.toNat hz
    simpa only [BitVec.toNat_setWidth, BitVec.toNat_zero] using ht
  · intro h
    have hz : (y-x).setWidth r = 0 := BitVec.eq_of_toNat_eq
      (by simpa only [BitVec.toNat_setWidth, BitVec.toNat_zero] using Nat.mod_eq_zero_of_dvd h)
    rw [hz, zero_add] at hadd
    simpa only [BitVec.toNat_setWidth] using congrArg BitVec.toNat hadd
-- CHECKPOINT

/-- XOR and wrapped subtraction have exactly the same 2-adic valuation
for two distinct words, including differences that wrap through zero. -/
theorem wordValuation_eq_sub (x y : Word) (hxy : x ≠ y) :
    wordValuation x y = padicValNat 2 (y-x).toNat := by
  have hx : x ^^^ y ≠ 0 := fun h => hxy (BitVec.xor_eq_zero_iff.mp h)
  have hy : y-x ≠ 0 := fun h => hxy (sub_eq_zero.mp h).symm
  have hn (w : Word) (hw : w ≠ 0) : w.toNat ≠ 0 := by
    intro h
    exact hw (BitVec.eq_of_toNat_eq h)
  have hb (w : Word) (hw : w ≠ 0) : padicValNat 2 w.toNat < 64 := by
    rw [← bitPolynomial_trailing_eq_padic w hw]
    exact (bitPolynomial_trailing w hw).1
  have hd (r : ℕ) (hr : r ≤ 64) :
      2^r ∣ (x ^^^ y).toNat ↔ 2^r ∣ (y-x).toNat :=
    (word_prefix_eq_iff_xor_dvd x y r).symm.trans (word_prefix_eq_iff_sub_dvd x y r hr)
  change padicValNat 2 (x ^^^ y).toNat = _
  apply Nat.le_antisymm
  · exact (padicValNat_dvd_iff_le (hn (y-x) hy)).mp
      ((hd _ (hb _ hx).le).mp pow_padicValNat_dvd)
  · exact (padicValNat_dvd_iff_le (hn (x ^^^ y) hx)).mp
      ((hd _ (hb _ hy).le).mpr pow_padicValNat_dvd)
-- CHECKPOINT

end ProvenHashes.UMASH
