import ProvenHashes.UMASHTagDenseMask
import ProvenHashes.UMASHDivisorBound

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet

theorem word_xor_common_right (U V L : Word) :
    (U ^^^ L) ^^^ (V ^^^ L) = U ^^^ V := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases U.getLsbD i <;> cases V.getLsbD i <;> cases L.getLsbD i <;> rfl
-- CHECKPOINT

/-- A common XOR word satisfying a fixed projection has at most one
selected-bit fibre for each admissible pattern. -/
theorem common_xor_projection_count (U V : Word) (S : Finset Word)
    (hE : ∀ L ∈ S, (U ^^^ L).toNat%p = (V ^^^ L).toNat%p) :
    S.card ≤ (maskPatterns (U ^^^ V).toNat).card *
      2^(64-(maskBitSet 64 (U ^^^ V).toNat).card) := by
  let m := (U ^^^ V).toNat
  let T := maskPatterns m
  let G (z : ℕ) := S.filter (fun L => (U ^^^ L).toNat &&& m = z)
  have hlabel (L : Word) (hL : L ∈ S) : (U ^^^ L).toNat &&& m ∈ T := by
    have hh := congruent_pattern _ _ (U ^^^ L).isLt (V ^^^ L).isLt (hE L hL)
    simpa only [← BitVec.toNat_xor, word_xor_common_right, m, T] using hh
  have hf (z : ℕ) (_hz : z ∈ T) : (G z).card ≤ 2^(64-(maskBitSet 64 m).card) := by
    apply le_trans _ (mask_value_targets_card_le 64 m z)
    apply Finset.card_le_card_of_injOn (fun L : Word => (U ^^^ L).toNat)
    · intro L hL
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (U ^^^ L).isLt,
        (Finset.mem_filter.mp hL).2⟩
    · intro L _ L' _ he
      have hh := congrArg (fun z : Word => U ^^^ z) (BitVec.eq_of_toNat_eq he)
      simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using hh
  calc
    S.card = ∑ z ∈ T, (G z).card := Finset.card_eq_sum_card_fiberwise hlabel
    _ ≤ ∑ _z ∈ T, 2^(64-(maskBitSet 64 m).card) := Finset.sum_le_sum hf
    _ = _ := by simp only [Finset.sum_const, smul_eq_mul]; rfl
-- CHECKPOINT

def tagLowEvent (M H tag tag' L : Word) : Prop :=
  ((M ^^^ (H+tag)) ^^^ L).toNat%p = ((M ^^^ (H+tag')) ^^^ L).toNat%p

noncomputable def tagLowTargets (M H tag tag' : Word) : Finset Word :=
  Finset.univ.filter (tagLowEvent M H tag tag')

theorem tagLowEvent_mask (M H tag tag' L : Word)
    (h : tagLowEvent M H tag tag' L) : ((H+tag) ^^^ (H+tag')).toNat ∈ maskSet := by
  have hh := congruent_xor_mem_maskSet _ _
    (((M ^^^ (H+tag)) ^^^ L)).isLt (((M ^^^ (H+tag')) ^^^ L)).isLt h
  rw [← BitVec.toNat_xor, word_xor_common_right] at hh
  have hc : (M ^^^ (H+tag)) ^^^ (M ^^^ (H+tag')) = (H+tag) ^^^ (H+tag') := by
    simpa only [BitVec.xor_comm M] using word_xor_common_right (H+tag) (H+tag') M
  rwa [hc] at hh
-- CHECKPOINT

/-- The 54-bit mask condition leaves at most 8192 low-product words. -/
theorem tagLowTargets_card (M H tag tag' : Word) (hne : tag ≠ tag')
    (hcommon : tag.toNat/256 = tag'.toNat/256) :
    (tagLowTargets M H tag tag').card ≤ 8192 := by
  let T := tagLowTargets M H tag tag'
  change T.card ≤ 8192
  by_cases ht : T.Nonempty
  · obtain ⟨L,hL⟩ := ht
    have hE := (Finset.mem_filter.mp hL).2
    have hm := tagLowEvent_mask M H tag tag' L hE
    have hp := tag_mask_popcount_ge54 H tag tag' hne hcommon hm
    have hc : (M ^^^ (H+tag)) ^^^ (M ^^^ (H+tag')) = (H+tag) ^^^ (H+tag') := by
      simpa only [BitVec.xor_comm M] using word_xor_common_right (H+tag) (H+tag') M
    have hb := common_xor_projection_count (M ^^^ (H+tag)) (M ^^^ (H+tag')) T
      (fun L hL => (Finset.mem_filter.mp hL).2)
    rw [hc] at hb
    apply hb.trans
    have hpow : 2^(64-(maskBitSet 64 ((H+tag) ^^^ (H+tag')).toNat).card) ≤ 2^10 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.mul_le_mul (maskSet_patterns_le_eight _ hm) hpow).trans (by decide)
  · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
    simp
-- CHECKPOINT

/-- A zero high product cannot cross a tag boundary: the tags have equal
upper 56 bits before any high-product addition. -/
theorem tagLowEvent_zero_false (M tag tag' L : Word) (hne : tag ≠ tag')
    (hcommon : tag.toNat/256 = tag'.toNat/256) : ¬tagLowEvent M 0 tag tag' L := by
  intro h
  have he : ((M ^^^ L) ^^^ tag).toNat%p = ((M ^^^ L) ^^^ tag').toNat%p := by
    simpa only [tagLowEvent, zero_add, BitVec.xor_assoc, BitVec.xor_comm tag L,
      BitVec.xor_comm tag' L] using h
  have ht := masked_word_projection_top_ne (M ^^^ L) tag tag' hne he
  have hh := congrArg (fun n : ℕ => n/(2^52)) hcommon
  norm_num only [Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul] at hh
  exact ht hh
-- CHECKPOINT

/-- A nonzero ordinary product has at most one operand pair for each
positive divisor of its target. -/
theorem word_product_divisor_count (N : ℕ) (hN : 0 < N) (S : Finset Chunk)
    (hE : ∀ k ∈ S, k.1.toNat*k.2.toNat = N) : S.card ≤ N.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun k : Chunk => k.1.toNat)
  · intro k hk
    apply Nat.mem_divisors.mpr
    exact ⟨⟨k.2.toNat, (hE k hk).symm⟩, hN.ne'⟩
  · intro x hx y hy he
    change x.1.toNat = y.1.toNat at he
    have hpos : 0 < x.1.toNat := by
      have hp : 0 < x.1.toNat*x.2.toNat := by rw [hE x hx]; exact hN
      by_contra hh
      have hz : x.1.toNat = 0 := by omega
      simp [hz] at hp
    have hxy : x.1.toNat*x.2.toNat = x.1.toNat*y.2.toNat := by
      rw [hE x hx, he, hE y hy]
    exact Prod.ext (BitVec.eq_of_toNat_eq he)
      (BitVec.eq_of_toNat_eq (Nat.eq_of_mul_eq_mul_left hpos hxy))
-- CHECKPOINT

end ProvenHashes.UMASH
