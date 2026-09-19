import ProvenHashes.UMASHSecondaryChecksum
import ProvenHashes.UMASHJointBody

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul chunkCode

theorem different_length_checksum_probability (x y : Block) (hy : y.Valid)
    (hlt : x.chunks.length < y.chunks.length) :
    uniformProb (fun k : OHKey => checksum k x = checksum k y) ≤ (1:ℚ≥0)/q^2 := by
  have hyl : 0 < y.chunks.length ∧ y.chunks.length ≤ 16 := by
    rcases hy with ⟨_,_,h⟩; omega
  let ys := y.chunks.dropLast
  have hys : y.chunks = ys ++ [lastChunk y] :=
    block_chunks_split y (List.ne_nil_of_length_pos hyl.1)
  have hn : ys.length < 17 := by
    dsimp only [ys]; rw [List.length_dropLast]; omega
  let j : Fin 17 := ⟨ys.length,hn⟩
  have hxj : x.chunks.length ≤ j.val := by
    dsimp only [j,ys]; rw [List.length_dropLast]; omega
  rw [← uniformProb_equiv keyPairsEquiv.symm (fun k => checksum k x = checksum k y)]
  apply probability_le_of_update _ j
  intro K
  have hcx (v : Chunk) := checksum_update_later K x j hxj v
  have hcy (v : Chunk) : checksum (keyPairsEquiv.symm (Function.update K j v)) y =
      xorChunk (checksum (keyPairsEquiv.symm K) ⟨ys,0⟩) (xorChunk (lastChunk y) v) := by
    rw [checksum_append_last _ y ys (lastChunk y) hys,
      checksum_update_later K ⟨ys,0⟩ j le_rfl v, keyPair_of_pairs _ ys.length hn]
    simp [j]
  let f := fun v : Chunk =>
    xorChunk (checksum (keyPairsEquiv.symm K) ⟨ys,0⟩) (xorChunk (lastChunk y) v)
  have hi : Function.Injective f :=
    (xorChunk_fixed_injective _).comp (xorChunk_fixed_injective _)
  simp only [hcx, hcy]
  have h := injective_target_probability f hi {checksum (keyPairsEquiv.symm K) x}
    (fun v => checksum (keyPairsEquiv.symm K) x = f v)
    (fun v hv => Finset.mem_singleton.mpr hv.symm)
  simpa only [Finset.card_singleton, Nat.cast_one, Fintype.card_prod, word_card,
    Nat.cast_mul, ← pow_two] using h
-- CHECKPOINT

theorem secondary_checksum_partition_bound (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16) :
    uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
      project (ohSecondary k y seed)) ≤
      uniformProb (fun k : OHKey => checksum k x = checksum k y)+(364816:ℚ≥0)/q := by
  let E := fun K : Fin 17 → Chunk =>
    checksum (keyPairsEquiv.symm K) x ≠ checksum (keyPairsEquiv.symm K) y
  let F := fun K : Fin 17 → Chunk =>
    project (ohSecondary (keyPairsEquiv.symm K) x seed) =
      project (ohSecondary (keyPairsEquiv.symm K) y seed)
  have hE (K : Fin 17 → Chunk) (v : Chunk) : E (Function.update K 16 v) ↔ E K := by
    dsimp only [E]
    rw [checksum_update_later K x 16 hx v, checksum_update_later K y 16 hy v]
  have hs := probability_and_update_event_le E F 16 ((364816:ℚ≥0)/q) hE
    (fun K hK => secondary_twist_different_checksum K seed x y hx hy hK)
  have hp : uniformProb (fun K => E K ∧ F K) ≤ (364816:ℚ≥0)/q :=
    hs.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (probability_le_one E) (show (0:ℚ≥0) ≤ 364816/q by positivity))
  have heq : uniformProb (fun K => ¬E K) =
      uniformProb (fun k : OHKey => checksum k x = checksum k y) := by
    simpa only [E, not_not] using uniformProb_equiv keyPairsEquiv.symm
      (fun k : OHKey => checksum k x = checksum k y)
  have hsplit : uniformProb F ≤ uniformProb (fun K => ¬E K)+
      uniformProb (fun K => E K ∧ F K) := by
    let G := fun b : Bool => if b then (fun K => ¬E K) else (fun K => E K ∧ F K)
    calc
      _ ≤ uniformProb (fun K => ∃ b ∈ (Finset.univ : Finset Bool), G b K) := by
        apply probability_mono
        intro K hK
        by_cases h : E K
        · exact ⟨false, Finset.mem_univ _, h, hK⟩
        · exact ⟨true, Finset.mem_univ _, h⟩
      _ ≤ ∑ b ∈ (Finset.univ : Finset Bool), uniformProb (G b) := probability_union_bound _ _
      _ = _ := by simp [G, add_comm]
  have heF : uniformProb F = uniformProb (fun k : OHKey =>
      project (ohSecondary k x seed) = project (ohSecondary k y seed)) :=
    uniformProb_equiv keyPairsEquiv.symm (fun k : OHKey =>
      project (ohSecondary k x seed) = project (ohSecondary k y seed))
  rw [heF, heq] at hsplit
  exact hsplit.trans (add_le_add_left hp _)
-- CHECKPOINT

theorem secondary_different_chunk_counts_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : ¬sameCount x y) :
    uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
      project (ohSecondary k y seed)) ≤ (729632:ℚ≥0)/q := by
  have hxl : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hyl : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  have hcheck : uniformProb (fun k : OHKey => checksum k x = checksum k y) ≤ (1:ℚ≥0)/q^2 := by
    rcases lt_or_gt_of_ne hc with h | h
    · exact different_length_checksum_probability x y hy h
    · simpa only [eq_comm] using different_length_checksum_probability y x hx h
  calc
    _ ≤ uniformProb (fun k : OHKey => checksum k x = checksum k y)+(364816:ℚ≥0)/q :=
      secondary_checksum_partition_bound seed x y hxl hyl
    _ ≤ (1:ℚ≥0)/q^2+(364816:ℚ≥0)/q := add_le_add_right hcheck _
    _ ≤ _ := by apply NNRat.coe_le_coe.mp; norm_num [q]
-- CHECKPOINT

end ProvenHashes.UMASH
