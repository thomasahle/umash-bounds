import ProvenHashes.UMASHTwoPHAtoms

/-! The low-bit compatibility restriction for the two-PH argument from the
GPT-6 Pro handoff of 2026-09-19, restricted joint reduction §1.2. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem phShuffleLane_prefix {n : ℕ} (s r : ℕ) (x : BitVec n)
    (hr : r ≤ n) (hs : s = 1 ∨ r ≤ s) :
    (phShuffleLane s x).toNat%2^r = (x <<< 1).toNat%2^r := by
  by_cases h1 : s = 1
  · simp [phShuffleLane, h1]
  · have hrs : r ≤ s := hs.resolve_left h1
    have hz : (x <<< s).toNat%2^r = 0 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hr)]
      apply Nat.mod_eq_zero_of_dvd
      exact dvd_mul_of_dvd_right (pow_dvd_pow 2 hrs) _
    simp only [phShuffleLane, h1, ↓reduceIte, BitVec.toNat_xor, Nat.xor_mod_two_pow, hz,
      Nat.xor_zero]
-- CHECKPOINT

theorem two_ph_lane_compatibility (s t r : ℕ) (ht : 0 < t) (hst : t < s)
    (hr : r ≤ 64) (hrh : r ≤ phDifferenceShift s t) (a b c d : Word) :
    (((phShuffleLane s a ^^^ phShuffleLane t b ^^^ d) ^^^
      ((a ^^^ b ^^^ c) <<< 1)).toNat)%2^r = (d ^^^ (c <<< 1)).toNat%2^r := by
  have hs : r ≤ s := by unfold phDifferenceShift at hrh; split_ifs at hrh <;> omega
  have ht' : t = 1 ∨ r ≤ t := by
    by_cases h1 : t = 1
    · exact Or.inl h1
    · exact Or.inr (by simpa only [phDifferenceShift, h1, ↓reduceIte] using hrh)
  simp only [BitVec.shiftLeft_xor_distrib, BitVec.toNat_xor, Nat.xor_mod_two_pow,
    phShuffleLane_prefix s r a hr (Or.inr hs), phShuffleLane_prefix t r b hr ht']
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_xor, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

/-- At three bits the compatibility condition is an eight-bin census,
regardless of the full shift loss h. -/
theorem two_ph_three_bit_compatibility (s t : ℕ) (ht : 0 < t) (hst : t < s)
    (hh : 3 ≤ phDifferenceShift s t) (a b c d : Word) :
    ((phShuffleLane s a ^^^ phShuffleLane t b ^^^ d).toNat ^^^
      (2*(a ^^^ b ^^^ c).toNat))%8 = (d ^^^ (c <<< 1)).toNat%8 := by
  have he := two_ph_lane_compatibility s t 3 ht hst (by decide) hh a b c d
  change ((phShuffleLane s a ^^^ phShuffleLane t b ^^^ d).toNat ^^^
      (2*(a ^^^ b ^^^ c).toNat))%2^3 = (d ^^^ (c <<< 1)).toNat%2^3
  simpa only [BitVec.toNat_xor, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_one,
    Nat.mod_mod_of_dvd _ (by norm_num : 8 ∣ 2^64), Nat.xor_mod_two_pow,
    Nat.mul_comm] using he
-- CHECKPOINT

end ProvenHashes.UMASH
