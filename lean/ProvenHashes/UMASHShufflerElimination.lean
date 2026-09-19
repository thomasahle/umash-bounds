import ProvenHashes.UMASHMaskRefinements
import ProvenHashes.UMASHModel

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet

/-- The nonfinal shuffler on a single lane, with the reference's s=1 case. -/
def phShuffleLane {n : ℕ} (s : ℕ) (x : BitVec n) : BitVec n :=
  if s = 1 then x <<< 1 else (x <<< 1) ^^^ (x <<< s)

/-- Triangular elimination is width-uniform: I+S is injective whenever every
shift used by S is strictly positive. -/
theorem phShuffleLane_add_self_injective (n s : ℕ) (hs : 0 < s) :
    Function.Injective (fun x : BitVec n => x ^^^ phShuffleLane s x) := by
  intro x y he
  have hbits : ∀ i, i < n → x.getLsbD i = y.getLsbD i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hin
      have hshift (k : ℕ) (hk : 0 < k) : (x <<< k).getLsbD i = (y <<< k).getLsbD i := by
        rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
        by_cases hik : i < k
        · simp only [hik, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
        · rw [ih (i-k) (by omega) (by omega)]
      have hb := congrArg (fun z : BitVec n => z.getLsbD i) he
      simp only [BitVec.getLsbD_xor] at hb
      have hS : (phShuffleLane s x).getLsbD i = (phShuffleLane s y).getLsbD i := by
        unfold phShuffleLane
        split
        · exact hshift 1 (by decide)
        · simp only [BitVec.getLsbD_xor, hshift 1 (by decide), hshift s hs]
      rw [hS] at hb
      exact Bool.xor_left_inj.mp hb
  exact BitVec.eq_of_getLsbD_eq hbits
-- CHECKPOINT

/-- Prescribing both compressor masks determines the PH and ENH differences
uniquely; this does not assert independence between compressors. -/
theorem shuffler_elimination_unique (n s : ℕ) (hs : 0 < s)
    (x e x' e' : BitVec n)
    (hu : x ^^^ e = x' ^^^ e')
    (hv : phShuffleLane s x ^^^ e = phShuffleLane s x' ^^^ e') :
    x = x' ∧ e = e' := by
  have hi : x ^^^ phShuffleLane s x = x' ^^^ phShuffleLane s x' := by
    have hh := congrArg₂ (fun a b : BitVec n => a ^^^ b) hu hv
    have cancel (a b c : BitVec n) : (a ^^^ b) ^^^ (c ^^^ b) = a ^^^ c := by
      rw [BitVec.xor_comm c b, BitVec.xor_assoc, ← BitVec.xor_assoc b b c,
        BitVec.xor_self, BitVec.zero_xor]
    simpa only [cancel] using hh
  have hx := phShuffleLane_add_self_injective n s hs hi
  subst x'
  exact ⟨rfl, (BitVec.xor_right_inj x).mp hu⟩
-- CHECKPOINT

theorem phShuffleLane_inverse_exists (n s : ℕ) (hs : 0 < s) (u : BitVec n) :
    ∃! x : BitVec n, x ^^^ phShuffleLane s x = u := by
  letI : Fintype (BitVec n) := Fintype.ofEquiv (Fin (2^n)) BitVec.equivFin.symm.toEquiv
  have hi := phShuffleLane_add_self_injective n s hs
  obtain ⟨x,hx⟩ := (Finite.surjective_of_injective hi) u
  exact ⟨x,hx,fun y hy => hi (hy.trans hx.symm)⟩
-- CHECKPOINT

theorem mask_word_mod16_zero (x : Word) (hx : x.toNat ∈ maskSet) (h16 : x.toNat%16 = 0) :
    x = 0 := by
  have hh : x.toNat ∈ maskSet.filter (fun m => m%16 = 0) := Finset.mem_filter.mpr ⟨hx,h16⟩
  rw [maskSet_mod_sixteen, Finset.mem_singleton] at hh
  exact BitVec.eq_of_toNat_eq hh
-- CHECKPOINT

theorem word_shift_mod16_zero (x : Word) (h16 : x.toNat%16 = 0) (s : ℕ) :
    (x <<< s).toNat%16 = 0 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_mod_of_dvd _ (by norm_num : 16 ∣ 2^64), Nat.mul_mod, h16]
  simp
-- CHECKPOINT

theorem phShuffleLane_mod16_zero (s : ℕ) (x : Word) (h16 : x.toNat%16 = 0) :
    (phShuffleLane s x).toNat%16 = 0 := by
  unfold phShuffleLane
  split
  · exact word_shift_mod16_zero x h16 1
  · rw [BitVec.toNat_xor]
    change ((x <<< 1).toNat ^^^ (x <<< s).toNat)%2^4 = 0
    rw [Nat.xor_mod_two_pow, word_shift_mod16_zero x h16 1,
      word_shift_mod16_zero x h16 s, Nat.xor_self]
-- CHECKPOINT

/-- PROOF2 reduction (8), under the exact low-divisibility conditions it uses.
No common-offset assumption is made for the two compressors. -/
theorem phenh_low_reduction (s : ℕ) (hs : 0 < s) (x e : Word)
    (hx : 16 ∣ x.toNat) (he : 16 ∣ e.toNat)
    (hu : (x ^^^ e).toNat ∈ maskSet)
    (hv : (phShuffleLane s x ^^^ e).toNat ∈ maskSet) : x = 0 ∧ e = 0 := by
  have hx0 : x.toNat%16 = 0 := Nat.mod_eq_zero_of_dvd hx
  have he0 : e.toNat%16 = 0 := Nat.mod_eq_zero_of_dvd he
  have hu0 : x ^^^ e = 0 := by
    apply mask_word_mod16_zero _ hu
    rw [BitVec.toNat_xor]
    change (x.toNat ^^^ e.toNat)%2^4 = 0
    rw [Nat.xor_mod_two_pow, hx0, he0, Nat.xor_self]
  have hv0 : phShuffleLane s x ^^^ e = 0 := by
    apply mask_word_mod16_zero _ hv
    rw [BitVec.toNat_xor]
    change ((phShuffleLane s x).toNat ^^^ e.toNat)%2^4 = 0
    rw [Nat.xor_mod_two_pow, phShuffleLane_mod16_zero s x hx0, he0, Nat.xor_self]
  exact shuffler_elimination_unique 64 s hs x e 0 0 (by simpa using hu0)
    (by simpa [phShuffleLane] using hv0)
-- CHECKPOINT

end ProvenHashes.UMASH
