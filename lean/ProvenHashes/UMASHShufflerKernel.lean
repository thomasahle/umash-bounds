import ProvenHashes.UMASHShufflerElimination
import ProvenHashes.UMASHProduct

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

/-- Decode an XOR/left-shift from its low bits upwards. -/
theorem xor_left_shift_injective (n s : ℕ) (hs : 0 < s) :
    Function.Injective (fun x : BitVec n => x ^^^ (x <<< s)) := by
  intro x y h
  have hb : ∀ i, x.getLsbD i = y.getLsbD i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      have he := congrArg (fun z : BitVec n => z.getLsbD i) h
      simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft] at he
      by_cases hi : i < s
      · simpa only [hi, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.xor_false] using he
      · have hh := ih (i-s) (by omega)
        simpa only [hh, Bool.xor_left_inj] using he
  exact BitVec.eq_of_getLsbD_eq (fun i _ => hb i)
-- CHECKPOINT

/-- Every nonfinal PH shuffler has exactly the same fibres as the
one-bit lane shift. This includes the special s=1 case. -/
theorem phShuffleLane_eq_iff_shift (n s : ℕ) (hs : 0 < s) (x y : BitVec n) :
    phShuffleLane s x = phShuffleLane s y ↔ x <<< 1 = y <<< 1 := by
  by_cases h1 : s = 1
  · simp only [phShuffleLane, h1, ↓reduceIte]
  · have hpos : 0 < s-1 := by omega
    have hf (z : BitVec n) :
        phShuffleLane s z = (z <<< 1) ^^^ ((z <<< 1) <<< (s-1)) := by
      simp only [phShuffleLane, h1, ↓reduceIte, ← BitVec.shiftLeft_add]
      rw [show 1+(s-1) = s by omega]
    rw [hf x, hf y]
    exact (xor_left_shift_injective n (s-1) hpos).eq_iff
-- CHECKPOINT

theorem word_shift_one_kernel (x : Word) :
    x <<< 1 = 0 ↔ x = 0 ∨ x = BitVec.ofNat 64 (2^63) := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at hn
    have hb := x.isLt
    norm_num at hn hb
    have hm : x.toNat%9223372036854775808 = 0 := by
      have hh : 2*(x.toNat%9223372036854775808) = 0 := by
        rw [← Nat.mul_mod_mul_left]
        simpa only [Nat.mul_comm] using hn
      omega
    have hc : x.toNat = 0 ∨ x.toNat = 9223372036854775808 := by omega
    rcases hc with hc | hc
    · exact Or.inl (BitVec.eq_of_toNat_eq hc)
    · exact Or.inr (BitVec.eq_of_toNat_eq hc)
  · rintro (rfl | rfl) <;> decide
-- CHECKPOINT

theorem phShuffleLane_kernel (s : ℕ) (hs : 0 < s) (x : Word) :
    phShuffleLane s x = 0 ↔ x = 0 ∨ x = BitVec.ofNat 64 (2^63) := by
  have hz : phShuffleLane s (0:Word) = 0 := by simp [phShuffleLane]
  rw [← word_shift_one_kernel]
  simpa only [hz, BitVec.zero_shiftLeft] using phShuffleLane_eq_iff_shift 64 s hs x 0
-- CHECKPOINT

theorem split_join (x : Chunk) : split (join x) = x := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    interval_cases i <;> simp [split, join]
-- CHECKPOINT

def phShuffleWide (s : ℕ) (x : Wide) : Wide :=
  join (phShuffleLane s (split x).1, phShuffleLane s (split x).2)

/-- The kernel on BitVec 128 is the binary span of the two lane top bits. -/
theorem phShuffleWide_kernel (s : ℕ) (hs : 0 < s) (x : Wide) :
    phShuffleWide s x = 0 ↔
      x = 0 ∨ x = BitVec.ofNat 128 (2^63) ∨ x = BitVec.ofNat 128 (2^127) ∨
        x = BitVec.ofNat 128 (2^63+2^127) := by
  constructor
  · intro h
    have hh := congrArg split h
    rw [phShuffleWide, split_join] at hh
    have h0 : phShuffleLane s (split x).1 = 0 := congrArg Prod.fst hh
    have h1 : phShuffleLane s (split x).2 = 0 := congrArg Prod.snd hh
    rw [phShuffleLane_kernel s hs] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · have hx := join_split x
      rw [show split x = (0,0) from Prod.ext h0 h1] at hx
      exact Or.inl hx.symm
    · have hx := join_split x
      rw [show split x = (0,BitVec.ofNat 64 (2^63)) from Prod.ext h0 h1] at hx
      exact Or.inr (Or.inr (Or.inl hx.symm))
    · have hx := join_split x
      rw [show split x = (BitVec.ofNat 64 (2^63),0) from Prod.ext h0 h1] at hx
      exact Or.inr (Or.inl hx.symm)
    · have hx := join_split x
      rw [show split x = (BitVec.ofNat 64 (2^63),BitVec.ofNat 64 (2^63)) from Prod.ext h0 h1] at hx
      exact Or.inr (Or.inr (Or.inr hx.symm))
  · intro h
    have hz : ∀ z : Word, z = 0 ∨ z = BitVec.ofNat 64 (2^63) → phShuffleLane s z = 0 :=
      fun z hz => (phShuffleLane_kernel s hs z).mpr hz
    rcases h with rfl | rfl | rfl | rfl <;>
      unfold phShuffleWide <;>
      rw [hz _ (by decide), hz _ (by decide)] <;> rfl
-- CHECKPOINT

end ProvenHashes.UMASH
