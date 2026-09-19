import ProvenHashes.UMASHCorrectedObligations

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

/-- Decode an XOR/right-shift from its high bits downwards. -/
theorem xor_right_shift_injective (w s : ℕ) (hs : 0 < s) :
    Function.Injective (fun x : BitVec w => x ^^^ (x >>> s)) := by
  intro x y h
  have hb (n : ℕ) : ∀ i, w-i = n → x.getLsbD i = y.getLsbD i := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hni
      by_cases hi : i < w
      · have hh : x.getLsbD (i+s) = y.getLsbD (i+s) :=
          ih (w-(i+s)) (by omega) (i+s) rfl
        have he := congrArg (fun z : BitVec w => z.getLsbD i) h
        simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight] at he
        simpa only [Nat.add_comm s i, hh, Bool.xor_left_inj] using he
      · rw [BitVec.getLsbD_of_ge x i (by omega), BitVec.getLsbD_of_ge y i (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  exact hb (w-i) i rfl
-- CHECKPOINT

/-- A supplied modular inverse gives a literal word-multiplication decoder. -/
theorem word_mul_injective (c d : Word) (hcd : c*d = 1) :
    Function.Injective (fun x : Word => x*c) := by
  intro x y h
  have he := congrArg (fun z : Word => z*d) h
  simpa [BitVec.mul_assoc, hcd] using he
-- CHECKPOINT

def shortPrepare (x : Word) : Word :=
  let h := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9
  h ^^^ (h >>> 27)

def shortFinish (x : Word) : Word :=
  let h := x * 0x94D049BB133111EB
  h ^^^ (h >>> 31)

theorem shortPrepare_injective : Function.Injective shortPrepare := by
  have hm := word_mul_injective 0xBF58476D1CE4E5B9 0x96DE1B173F119089 (by decide)
  exact (xor_right_shift_injective 64 27 (by omega)).comp
    (hm.comp (xor_right_shift_injective 64 30 (by omega)))
-- CHECKPOINT

theorem shortFinish_injective : Function.Injective shortFinish := by
  have hm := word_mul_injective 0x94D049BB133111EB 0x319642B2D24D8EC3 (by decide)
  exact (xor_right_shift_injective 64 31 (by omega)).comp hm
-- CHECKPOINT

theorem shortHash_eq_mixer (k : OHKey) (seed : Word) (m : Message) :
    shortHash k seed m false =
      shortFinish (shortPrepare (shortPack m) ^^^ (seed + keyWord k m.length)) := by
  simp only [shortHash, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    shortFinish, shortPrepare]
-- CHECKPOINT

end ProvenHashes.UMASH
