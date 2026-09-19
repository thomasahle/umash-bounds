import ProvenHashes.UMASHTagLowTargets
import ProvenHashes.UMASHTagProbability
import ProvenHashes.UMASHKeyAcceptance

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype tagLowTargets

def tagProductHigh (k : Chunk) : Word := BitVec.ofNat 64 (k.1.toNat*k.2.toNat/q)
def tagProductLow (k : Chunk) : Word := BitVec.ofNat 64 (k.1.toNat*k.2.toNat%q)

theorem tag_product_reconstruct (k : Chunk) :
    k.1.toNat*k.2.toNat = q*(tagProductHigh k).toNat+(tagProductLow k).toNat := by
  have hp : k.1.toNat*k.2.toNat < q*q := Nat.mul_lt_mul_of_lt_of_lt k.1.isLt k.2.isLt
  have hH : k.1.toNat*k.2.toNat/q < q := (Nat.div_lt_iff_lt_mul (by norm_num [q])).mpr hp
  change k.1.toNat*k.2.toNat =
    q*((k.1.toNat*k.2.toNat/q)%q)+((k.1.toNat*k.2.toNat%q)%q)
  rw [Nat.mod_eq_of_lt hH, Nat.mod_mod]
  exact (Nat.mod_add_div _ _).symm.trans (Nat.add_comm _ _)
-- CHECKPOINT

theorem enh_tag_low_event (k M : Chunk) (tag tag' : Word)
    (hE : project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))) :
    tagLowEvent M.2 (tagProductHigh k) tag tag' (tagProductLow k) := by
  have hp := congrArg (fun z : Field × Field => z.2.val) hE
  simp only [project, ZMod.val_natCast, xorChunk, enh_high_as_word, zero_add] at hp
  simpa only [tagLowEvent, tagProductHigh, tagProductLow, BitVec.xor_assoc] using hp
-- CHECKPOINT

/-- Fix H, count at most 8192 possible L, and apply the strict divisor bound
to each ordinary product qH+L. -/
theorem enh_tag_high_fibre_count (M : Chunk) (tag tag' H : Word)
    (hne : tag ≠ tag') (hcommon : tag.toNat/256 = tag'.toNat/256)
    (S : Finset Chunk) (hH : ∀ k ∈ S, tagProductHigh k = H)
    (hE : ∀ k ∈ S, project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))) :
    S.card ≤ 8192*(2^36-1) := by
  have hlabel (k : Chunk) (hk : k ∈ S) :
      tagProductLow k ∈ tagLowTargets M.2 H tag tag' := by
    unfold tagLowTargets
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hH k hk] using enh_tag_low_event k M tag tag' (hE k hk)
  by_cases hz : H = 0
  · have hs : S = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro k hk
      have hl₀ := hlabel k hk
      unfold tagLowTargets at hl₀
      have hl := (Finset.mem_filter.mp hl₀).2
      rw [hz] at hl
      exact tagLowEvent_zero_false M.2 tag tag' (tagProductLow k) hne hcommon hl
    rw [hs]
    simp
  · have hHpos : 0 < H.toNat := by
      have hn : H.toNat ≠ 0 := fun h => hz (BitVec.eq_of_toNat_eq h)
      omega
    let G (L : Word) := S.filter (fun k => tagProductLow k = L)
    have hf (L : Word) (_hL : L ∈ tagLowTargets M.2 H tag tag') :
        (G L).card ≤ 2^36-1 := by
      let N := q*H.toNat+L.toNat
      have hN : 0 < N := by
        dsimp [N]
        have : 0 < q := by norm_num [q]
        positivity
      have hN128 : N < 2^128 := by
        have hh := H.isLt
        have hl := L.isLt
        dsimp [N]
        norm_num [q] at hh hl ⊢
        omega
      have hc := word_product_divisor_count N hN (G L) (by
        intro k hk
        have hkS := (Finset.mem_filter.mp hk).1
        rw [tag_product_reconstruct, hH k hkS, (Finset.mem_filter.mp hk).2])
      have hd := divisors_card_lt_two_pow36 N hN hN128
      omega
    calc
      S.card = ∑ L ∈ tagLowTargets M.2 H tag tag', (G L).card :=
        Finset.card_eq_sum_card_fiberwise hlabel
      _ ≤ ∑ _L ∈ tagLowTargets M.2 H tag tag', (2^36-1) := Finset.sum_le_sum hf
      _ = (tagLowTargets M.2 H tag tag').card*(2^36-1) := by
        simp only [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (tagLowTargets_card M.2 H tag tag' hne hcommon)
-- CHECKPOINT

/-- The old 4096-element boundary cover suffices because each nonzero
product has at most 2^36-1 divisor pairs. -/
theorem enh_tag_sharp_count_ordered (M : Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (horder : tag.toNat ≤ tag'.toNat)
    (hcommon : tag.toNat/256 = tag'.toNat/256) (S : Finset Chunk)
    (hE : ∀ k ∈ S, project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))) :
    S.card ≤ 4096*8192*(2^36-1) := by
  let T := tagBoundaryTargets tag
  let G (H : Word) := S.filter (fun k => tagProductHigh k = H)
  have hlabel (k : Chunk) (hk : k ∈ S) : tagProductHigh k ∈ T :=
    enh_tag_boundary k M tag tag' hne horder hcommon (hE k hk)
  have hf (H : Word) (_hH : H ∈ T) : (G H).card ≤ 8192*(2^36-1) :=
    enh_tag_high_fibre_count M tag tag' H hne hcommon (G H)
      (fun k hk => (Finset.mem_filter.mp hk).2)
      (fun k hk => hE k (Finset.mem_filter.mp hk).1)
  calc
    S.card = ∑ H ∈ T, (G H).card := Finset.card_eq_sum_card_fiberwise hlabel
    _ ≤ ∑ _H ∈ T, 8192*(2^36-1) := Finset.sum_le_sum hf
    _ = T.card*(8192*(2^36-1)) := by simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ 4096*(8192*(2^36-1)) := Nat.mul_le_mul_right _ (tagBoundaryTargets_card tag)
    _ = _ := by ring
-- CHECKPOINT

/-- A quantitative count bound leaves the strict 1/(8q) inequality intact. -/
theorem masked_enh_tag_sharp_ordered (M : Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (horder : tag.toNat ≤ tag'.toNat)
    (hcommon : tag.toNat/256 = tag'.toNat/256) :
    uniformProb (fun k : Chunk => project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))) ≤
        ((4096*8192*(2^36-1):ℕ):ℚ≥0)/q^2 := by
  have hc := enh_tag_sharp_count_ordered M tag tag' hne horder hcommon
    (Finset.univ.filter (fun k : Chunk => project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))))
    (fun k hk => (Finset.mem_filter.mp hk).2)
  unfold uniformProb
  simp only [Fintype.card_prod, word_card, Nat.cast_mul, pow_two]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hc
-- CHECKPOINT

end ProvenHashes.UMASH
