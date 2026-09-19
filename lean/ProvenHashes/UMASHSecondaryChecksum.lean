import ProvenHashes.UMASHEvenPHSlice
import ProvenHashes.UMASHTwistWeights

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

/-- The refined PH projection bound permits different fixed XOR offsets. -/
theorem masked_ph_refined_probability (x y M N : Chunk) (hxy : x ≠ y) :
    uniformProb (fun k : Chunk => project (xorChunk M (ph k x)) =
      project (xorChunk N (ph k y))) ≤ (364816:ℚ≥0)/q := by
  by_cases hx : x.1 ≠ y.1
  · apply probability_prod_le
    intro fixed
    by_cases ho : (x.1 ^^^ y.1).toNat%2 = 1
    · exact (masked_ph_odd_right_probability x y M N fixed ho).trans (by apply NNRat.coe_le_coe.mp; norm_num [q])
    · exact masked_ph_even_right_probability x y M N fixed hx (by omega)
  · have hy : x.2 ≠ y.2 := fun h => hxy (Prod.ext (not_ne_iff.mp hx) h)
    rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => project (xorChunk M (ph k x)) = project (xorChunk N (ph k y)))]
    apply probability_prod_le
    intro fixed
    by_cases ho : (x.2 ^^^ y.2).toNat%2 = 1
    · exact (masked_ph_odd_left_probability x y M N fixed ho).trans (by apply NNRat.coe_le_coe.mp; norm_num [q])
    · exact masked_ph_even_left_probability x y M N fixed hy (by omega)
-- CHECKPOINT

theorem checksum_eq_iff_data_checksum (k : OHKey) (x y : Block) (hc : sameCount x y) :
    checksum k x = checksum k y ↔ dataChecksum x = dataChecksum y := by
  constructor
  · intro h
    have hh := congrArg chunkCode h
    rw [checksum_code_split, checksum_code_split] at hh
    change x.chunks.length = y.chunks.length at hc
    rw [hc] at hh
    exact chunkCode_injective (add_right_cancel hh)
  · exact checksum_eq_of_data_checksum k x y hc
-- CHECKPOINT

/-- PROOF5 Lemma 4.1 on the actual two fresh twisting key words. -/
theorem secondary_twist_different_checksum (K : Fin 17 → Chunk) (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16)
    (hne : checksum (keyPairsEquiv.symm K) x ≠ checksum (keyPairsEquiv.symm K) y) :
    uniformProb (fun v : Chunk =>
      project (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) x seed) =
      project (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) y seed)) ≤
      (364816:ℚ≥0)/q := by
  simp only [secondary_twist_slice K x seed hx, secondary_twist_slice K y seed hy]
  exact masked_ph_refined_probability _ _ _ _ hne
-- CHECKPOINT

theorem secondary_checksum_different_bound (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16)
    (hne : ∀ k : OHKey, checksum k x ≠ checksum k y) :
    uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
      project (ohSecondary k y seed)) ≤ (364816:ℚ≥0)/q := by
  rw [← uniformProb_equiv keyPairsEquiv.symm
    (fun k => project (ohSecondary k x seed) = project (ohSecondary k y seed))]
  apply probability_le_of_update _ (16:Fin 17)
  intro K
  exact secondary_twist_different_checksum K seed x y hx hy (hne _)
-- CHECKPOINT

theorem secondary_different_data_checksum_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hne : dataChecksum x ≠ dataChecksum y) :
    uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
      project (ohSecondary k y seed)) ≤ (364816:ℚ≥0)/q := by
  have hxl : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hyl : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  exact secondary_checksum_different_bound seed x y hxl hyl
    (fun k he => hne ((checksum_eq_iff_data_checksum k x y hc).mp he))
-- CHECKPOINT

theorem secondary_enh_only_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hp : phDiffCount x y = 0) (hne : lastChunk x ≠ lastChunk y) :
    uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
      project (ohSecondary k y seed)) ≤ (364816:ℚ≥0)/q := by
  have hxl : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨_,_,h⟩; omega
  have hyl : 0 < y.chunks.length ∧ y.chunks.length ≤ 16 := by
    rcases hy with ⟨_,_,h⟩; omega
  exact secondary_checksum_different_bound seed x y hxl.2 hyl.2
    (fun k => checksum_ne_of_last k x y
      (List.ne_nil_of_length_pos hxl.1) (List.ne_nil_of_length_pos hyl.1)
      (phDiffCount_zero_prefix x y hc hp) hne)
-- CHECKPOINT

end ProvenHashes.UMASH
