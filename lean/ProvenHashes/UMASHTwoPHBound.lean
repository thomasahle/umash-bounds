import ProvenHashes.UMASHTwoPHLedger
import ProvenHashes.UMASHTwoPHAffine
import ProvenHashes.UMASHTwoPHBlockMasks
import ProvenHashes.UMASHTwoPHIndices

/-! Closure of the hard equal-checksum two-PH row. The shuffler elimination
argument is from the GPT-6 Pro handoff of 2026-09-19, restricted joint
reduction §1.2. The weighted three-bit census replaces its long-mask split,
using the previously proved low/high twisting weights. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet

theorem two_ph_block_slice_bound (K : Fin 17 → Chunk) (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hc : sameCount x y) (hsum : dataChecksum x = dataChecksum y)
    (i j : ℕ) (hij : i < j) (hj : j+1 < x.chunks.length)
    (hdi : x.chunks.getD i (0,0) ≠ y.chunks.getD i (0,0))
    (hdj : x.chunks.getD j (0,0) ≠ y.chunks.getD j (0,0)) :
    uniformProb (fun abw : (Chunk × Chunk) × Chunk => jointEvent seed x y
      (keyPairsEquiv.symm (Function.update
        (Function.update (Function.update K ⟨i, by omega⟩ abw.1.1) ⟨j, by omega⟩ abw.1.2)
        16 abw.2))) ≤ (1416246956032:ℚ≥0)/q^2 := by
  have hy : y.chunks.length ≤ 16 := by change x.chunks.length = y.chunks.length at hc; omega
  let s := x.chunks.length-(i+1)
  let t := x.chunks.length-(j+1)
  let h := phDifferenceShift s t
  have ht : 0 < t := by dsimp [t]; omega
  have hst : t < s := by dsimp [s,t]; omega
  have hs : s ≤ 15 := by dsimp [s]; omega
  have hh : h ≤ 15 := by dsimp [h,phDifferenceShift]; split_ifs <;> omega
  let K₂ (ab : Chunk × Chunk) := Function.update (Function.update K ⟨i, by omega⟩ ab.1) ⟨j, by omega⟩ ab.2
  let U (ab : Chunk × Chunk) := rawPrimaryMask (keyPairsEquiv.symm (K₂ ab)) seed x y
  let V (ab : Chunk × Chunk) := rawSecondaryMask (keyPairsEquiv.symm (K₂ ab)) seed x y
  obtain ⟨C,D,hraw⟩ := two_ph_block_raw_masks K seed x y hx hc i j hij hj
  let E (abw : (Chunk × Chunk) × Chunk) := jointEvent seed x y
    (keyPairsEquiv.symm (Function.update (K₂ abw.1) 16 abw.2))
  apply two_ph_weighted_partition E U V h
    ((D.1 ^^^ (C.1 <<< 1)).toNat%8) ((D.2 ^^^ (C.2 <<< 1)).toNat%8) hh
  · intro ab w he
    have hm := joint_event_raw_masks
      (keyPairsEquiv.symm (Function.update (K₂ ab) 16 w)) seed x y hc hsum he
    have hfixed := raw_masks_update_twist (K₂ ab) seed x y hx hy w
    rw [hfixed.1,hfixed.2] at hm
    have hP := Finset.mem_product.mp hm.1
    have hS := Finset.mem_product.mp hm.2
    exact ⟨hP.1,hS.1,hP.2,hS.2⟩
  · intro ab h3
    dsimp only [U,V,K₂]
    rw [(hraw ab.1 ab.2).1,(hraw ab.1 ab.2).2]
    exact two_ph_affine_compatibility s t ht hst h3 _ _ C D
  · intro u v
    dsimp only [U,V,K₂]
    simp_rw [fun a b => (hraw a b).1, fun a b => (hraw a b).2]
    exact two_ph_affine_atom _ _ _ _ C D u v hdi hdj s t ht hst (by omega)
  · intro ab
    apply le_min
    · apply (probability_mono ?_).trans (secondary_twist_low_weight (K₂ ab) seed x y hx hy hc hsum)
      intro w hw
      have he := congrArg (fun z : Field × Field => z.1.val) hw.2
      simpa only [project, ZMod.val_natCast] using he
    · apply (probability_mono ?_).trans (secondary_twist_high_weight (K₂ ab) seed x y hx hy hc hsum)
      intro w hw
      have he := congrArg (fun z : Field × Field => z.2.val) hw.2
      simpa only [project, ZMod.val_natCast] using he
-- CHECKPOINT

/-- The original exact obligation, now without any analytic premise. -/
theorem subcase_b_bound : SubcaseBBound := by
  intro seed x y hx hy hc hsum hp
  have hlen : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  obtain ⟨i,j,hij,hj,hdi,hdj⟩ := phDiffCount_two_indices x y hc hp
  let ip : Fin 17 := ⟨i, by omega⟩
  let jp : Fin 17 := ⟨j, by omega⟩
  have hipjp : ip ≠ jp := by intro he; have := congrArg Fin.val he; change i = j at this; omega
  have hip16 : ip ≠ 16 := by intro he; have := congrArg Fin.val he; change i = 16 at this; omega
  have hjp16 : jp ≠ 16 := by intro he; have := congrArg Fin.val he; change j = 16 at this; omega
  rw [← uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)]
  apply probability_le_of_three_updates _ ip jp 16 hipjp hip16 hjp16
  intro K
  rw [← uniformProb_equiv (Equiv.prodAssoc Chunk Chunk Chunk)]
  exact (two_ph_block_slice_bound K seed x y hlen hc hsum i j hij hj hdi hdj).trans_eq
    (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
