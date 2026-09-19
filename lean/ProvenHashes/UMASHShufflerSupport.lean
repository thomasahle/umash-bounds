import ProvenHashes.UMASHPHENHTargets

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet

/-- Every lane shuffler preserves a zero low-bit prefix, at arbitrary width. -/
theorem phShuffleLane_prefix_zero {n : ℕ} (s r : ℕ) (hr : r ≤ n)
    (x : BitVec n) (hx : x.toNat%2^r = 0) :
    (phShuffleLane s x).toNat%2^r = 0 := by
  have hshift (k : ℕ) : (x <<< k).toNat%2^r = 0 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hr), Nat.mul_mod, hx]
    simp
  unfold phShuffleLane
  split
  · exact hshift 1
  · rw [BitVec.toNat_xor, Nat.xor_mod_two_pow, hshift 1, hshift s, Nat.xor_self]
-- CHECKPOINT

/-- The executable inverse also preserves all required low zero bits.
This is proved at every width and does not enumerate word values. -/
theorem phShuffleInverse_prefix_zero {n : ℕ} (s r : ℕ) (hr : r ≤ n)
    (y : BitVec n) (hy : y.toNat%2^r = 0) :
    (phShuffleInverse s y).toNat%2^r = 0 := by
  have h (m : ℕ) : (phShuffleInverseAux s y m).toNat%2^r = 0 := by
    induction m with
    | zero => simp [phShuffleInverseAux]
    | succ m ih =>
      rw [phShuffleInverseAux, BitVec.toNat_xor, Nat.xor_mod_two_pow,
        hy, phShuffleLane_prefix_zero s r hr _ ih, Nat.xor_self]
  exact h n
-- CHECKPOINT

/-- Two raw low masks divisible by 2^r yield an ENH target divisible by
2^r, as required by the sharp low-target theorem. -/
theorem phenhENHMask_dvd (s r u v : ℕ) (hr : r ≤ 64)
    (hu : 2^r ∣ u) (hv : 2^r ∣ v) : 2^r ∣ phenhENHMask s u v := by
  have hword (a : ℕ) (ha : 2^r ∣ a) : (BitVec.ofNat 64 a).toNat%2^r = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hr)]
    exact Nat.mod_eq_zero_of_dvd ha
  have hinput : (BitVec.ofNat 64 u ^^^ BitVec.ofNat 64 v).toNat%2^r = 0 := by
    rw [BitVec.toNat_xor, Nat.xor_mod_two_pow, hword u hu, hword v hv, Nat.xor_self]
  have hx := phShuffleInverse_prefix_zero s r hr _ hinput
  apply Nat.dvd_of_mod_eq_zero
  unfold phenhENHMask phenhPHMask
  rw [BitVec.toNat_xor, Nat.xor_mod_two_pow, hword u hu, hx, Nat.xor_self]
-- CHECKPOINT

end ProvenHashes.UMASH
