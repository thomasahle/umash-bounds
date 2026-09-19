import ProvenHashes.UMASHTagBoundary

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem high_product_word_point (t : Word) :
    uniformProb (fun k : Chunk => BitVec.ofNat 64 (k.1.toNat*k.2.toNat/q) = t) ≤
      (65:ℚ≥0)/q := by
  apply (probability_mono ?_).trans (high_product_point_mass_le t.toNat)
  intro k hk
  have hprod : k.1.toNat*k.2.toNat < q*q := Nat.mul_lt_mul_of_lt_of_lt k.1.isLt k.2.isLt
  have hH : k.1.toNat*k.2.toNat/q < q :=
    (Nat.div_lt_iff_lt_mul (by norm_num [q])).mpr hprod
  have he := congrArg BitVec.toNat hk
  change (k.1.toNat*k.2.toNat/q)%q = t.toNat at he
  rwa [Nat.mod_eq_of_lt hH] at he
-- CHECKPOINT

theorem enh_tag_boundary (k M : Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (horder : tag.toNat ≤ tag'.toNat)
    (hcommon : tag.toNat/256 = tag'.toNat/256)
    (he : project (xorChunk M (enh k (0,0) tag)) = project (xorChunk M (enh k (0,0) tag'))) :
    BitVec.ofNat 64 (k.1.toNat*k.2.toNat/q) ∈ tagBoundaryTargets tag := by
  let H := BitVec.ofNat 64 (k.1.toNat*k.2.toNat/q)
  let L := BitVec.ofNat 64 (k.1.toNat*k.2.toNat%q)
  let C := M.2 ^^^ L
  have hf (t : Word) : (xorChunk M (enh k (0,0) t)).2 = C ^^^ (H+t) := by
    simp only [xorChunk, enh_high_as_word, zero_add, C, H, L]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  have hp := congrArg (fun z : Field × Field => z.2.val) he
  simp only [project, ZMod.val_natCast] at hp
  rw [hf tag, hf tag'] at hp
  have hn : H+tag ≠ H+tag' := by
    intro h
    exact hne (add_left_cancel h)
  exact tag_boundary_cover H tag tag' horder hcommon
    (masked_word_projection_top_ne C (H+tag) (H+tag') hn hp)
-- CHECKPOINT

theorem masked_enh_tag_probability_ordered (M : Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (horder : tag.toNat ≤ tag'.toNat)
    (hcommon : tag.toNat/256 = tag'.toNat/256) :
    uniformProb (fun k : Chunk => project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))) ≤ (266240:ℚ≥0)/q := by
  classical
  let T := tagBoundaryTargets tag
  let E (t : Word) (k : Chunk) := BitVec.ofNat 64 (k.1.toNat*k.2.toNat/q) = t
  calc
    _ ≤ uniformProb (fun k : Chunk => ∃ t ∈ T, E t k) := by
      apply probability_mono
      intro k hk
      exact ⟨_, enh_tag_boundary k M tag tag' hne horder hcommon hk, rfl⟩
    _ ≤ ∑ t ∈ T, uniformProb (E t) := probability_union_bound T E
    _ ≤ ∑ _t ∈ T, (65:ℚ≥0)/q :=
      Finset.sum_le_sum (fun t _ => high_product_word_point t)
    _ = T.card*((65:ℚ≥0)/q) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4096:ℚ≥0)*((65:ℚ≥0)/q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Nat.cast_le.mpr (tagBoundaryTargets_card tag)
    _ = (266240:ℚ≥0)/q := by ring
-- CHECKPOINT

theorem masked_enh_tag_probability (M data : Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (hcommon : tag.toNat/256 = tag'.toNat/256) :
    uniformProb (fun k : Chunk => project (xorChunk M (enh k data tag)) =
      project (xorChunk M (enh k data tag'))) ≤ (266240:ℚ≥0)/q := by
  have hzero : uniformProb (fun k : Chunk => project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))) ≤ (266240:ℚ≥0)/q := by
    rcases le_total tag.toNat tag'.toNat with hle | hle
    · exact masked_enh_tag_probability_ordered M tag tag' hne hle hcommon
    · have h := masked_enh_tag_probability_ordered M tag' tag hne.symm hle hcommon.symm
      simpa only [eq_comm] using h
  let e : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft data.1) (Equiv.addLeft data.2)
  have he (k : Chunk) (t : Word) : enh (e k) (0,0) t = enh k data t := by
    change enh (data.1+k.1, data.2+k.2) (0,0) t = enh k data t
    simp only [enh, zero_add]
  have hevent : (fun k : Chunk => project (xorChunk M (enh (e k) (0,0) tag)) =
      project (xorChunk M (enh (e k) (0,0) tag'))) =
      (fun k => project (xorChunk M (enh k data tag)) = project (xorChunk M (enh k data tag'))) := by
    funext k
    rw [he k tag, he k tag']
  rw [← hevent, uniformProb_equiv e (fun k : Chunk =>
    project (xorChunk M (enh k (0,0) tag)) = project (xorChunk M (enh k (0,0) tag')))]
  exact hzero
-- CHECKPOINT

end ProvenHashes.UMASH
