import ProvenHashes.UMASHTagProbability
import ProvenHashes.UMASHJointPrefixes

/-! The tag boundary implication permits a common XOR offset that depends on
the exposed key. This supplies the secondary marginal tag row of PROOF5. -/
namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem variable_mask_enh_tag_probability_ordered (M : Chunk → Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (horder : tag.toNat ≤ tag'.toNat)
    (hcommon : tag.toNat/256 = tag'.toNat/256) :
    uniformProb (fun k : Chunk => project (xorChunk (M k) (enh k (0,0) tag)) =
      project (xorChunk (M k) (enh k (0,0) tag'))) ≤ (266240:ℚ≥0)/q := by
  classical
  let T := tagBoundaryTargets tag
  let E (t : Word) (k : Chunk) := BitVec.ofNat 64 (k.1.toNat*k.2.toNat/q) = t
  calc
    _ ≤ uniformProb (fun k : Chunk => ∃ t ∈ T, E t k) := by
      apply probability_mono
      intro k hk
      exact ⟨_, enh_tag_boundary k (M k) tag tag' hne horder hcommon hk, rfl⟩
    _ ≤ ∑ t ∈ T, uniformProb (E t) := probability_union_bound T E
    _ ≤ ∑ _t ∈ T, (65:ℚ≥0)/q :=
      Finset.sum_le_sum (fun t _ => high_product_word_point t)
    _ = T.card*((65:ℚ≥0)/q) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4096:ℚ≥0)*((65:ℚ≥0)/q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Nat.cast_le.mpr (tagBoundaryTargets_card tag)
    _ = (266240:ℚ≥0)/q := by ring
-- CHECKPOINT

theorem variable_mask_enh_tag_probability (M : Chunk → Chunk) (data : Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (hcommon : tag.toNat/256 = tag'.toNat/256) :
    uniformProb (fun k : Chunk => project (xorChunk (M k) (enh k data tag)) =
      project (xorChunk (M k) (enh k data tag'))) ≤ (266240:ℚ≥0)/q := by
  let e : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft data.1) (Equiv.addLeft data.2)
  have hz : uniformProb (fun k : Chunk => project (xorChunk (M (e.symm k)) (enh k (0,0) tag)) =
      project (xorChunk (M (e.symm k)) (enh k (0,0) tag'))) ≤ (266240:ℚ≥0)/q := by
    rcases le_total tag.toNat tag'.toNat with hle | hle
    · exact variable_mask_enh_tag_probability_ordered _ tag tag' hne hle hcommon
    · simpa only [eq_comm] using
        variable_mask_enh_tag_probability_ordered (fun k => M (e.symm k))
          tag' tag hne.symm hle hcommon.symm
  rw [← uniformProb_equiv e (fun k : Chunk =>
    project (xorChunk (M (e.symm k)) (enh k (0,0) tag)) =
      project (xorChunk (M (e.symm k)) (enh k (0,0) tag')))] at hz
  have he (k : Chunk) (t : Word) : enh (e k) (0,0) t = enh k data t := by
    change enh (data.1+k.1, data.2+k.2) (0,0) t = enh k data t
    simp only [enh, zero_add]
  simpa only [Equiv.symm_apply_apply, he] using hz
-- CHECKPOINT

theorem secondary_tag_common_mask (k : OHKey) (seed : Word) (x y : Block)
    (xs : List Chunk) (last : Chunk) (hx : x.chunks = xs ++ [last])
    (hy : y.chunks = xs ++ [last]) :
    ∃ M : Chunk,
      ohSecondary k x seed = xorChunk M (enh (keyPair k xs.length) last (blockTag seed x)) ∧
      ohSecondary k y seed = xorChunk M (enh (keyPair k xs.length) last (blockTag seed y)) := by
  have hcheck : checksum k x = checksum k y := by simp only [checksum, hx, hy]
  refine ⟨xorChunk (secondaryPrefix k xs) (ph (keyPair k 16) (checksum k x)), ?_, ?_⟩
  · rw [ohSecondary_eq_body, secondaryBody_append_last k x seed xs last hx]
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
      simp [xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  · rw [ohSecondary_eq_body, secondaryBody_append_last k y seed xs last hy, ← hcheck]
    apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
      simp [xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

theorem secondary_tag_only_bound (seed : Word) (x y : Block) (hx : x.Valid)
    (hsame : x.chunks = y.chunks) (hne : blockTag seed x ≠ blockTag seed y) :
    uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
      project (ohSecondary k y seed)) ≤ (266240:ℚ≥0)/q := by
  classical
  have hxlen : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨_,_,h⟩; omega
  let xs := x.chunks.dropLast
  have hxs : x.chunks = xs ++ [lastChunk x] :=
    block_chunks_split x (List.ne_nil_of_length_pos hxlen.1)
  have hys : y.chunks = xs ++ [lastChunk x] := hsame.symm.trans hxs
  have hn : xs.length < 17 := by
    dsimp only [xs]; rw [List.length_dropLast]; omega
  let j : Fin 17 := ⟨xs.length,hn⟩
  rw [← uniformProb_equiv keyPairsEquiv.symm
    (fun k => project (ohSecondary k x seed) = project (ohSecondary k y seed))]
  apply probability_le_of_update _ j
  intro K
  have hs (v : Chunk) := secondary_tag_common_mask
    (keyPairsEquiv.symm (Function.update K j v)) seed x y xs (lastChunk x) hxs hys
  choose M hM hN using hs
  have hk (v : Chunk) : keyPair (keyPairsEquiv.symm (Function.update K j v)) xs.length = v := by
    rw [keyPair_of_pairs _ xs.length hn]
    simp [j]
  simp only [hM, hN, hk]
  exact variable_mask_enh_tag_probability M (lastChunk x) (blockTag seed x)
    (blockTag seed y) hne (blockTag_common_high seed x y)
-- CHECKPOINT

end ProvenHashes.UMASH
