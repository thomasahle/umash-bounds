import ProvenHashes.UMASHTagProbability

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem primary_tag_only_le (seed : Word) (x y : Block) (hx : x.Valid)
    (hsame : x.chunks = y.chunks) (hne : blockTag seed x ≠ blockTag seed y) :
    uniformProb (primaryEvent seed x y) ≤ (266240:ℚ≥0)/q := by
  have hxlen : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨h0,h256,hn⟩
    omega
  let xs := x.chunks.dropLast
  have hxs : x.chunks = xs ++ [lastChunk x] :=
    block_chunks_split x (List.ne_nil_of_length_pos hxlen.1)
  have hys : y.chunks = xs ++ [lastChunk x] := hsame.symm.trans hxs
  have hn : xs.length < 17 := by
    dsimp only [xs]
    rw [List.length_dropLast]
    omega
  let j : Fin 17 := ⟨xs.length,hn⟩
  rw [← uniformProb_equiv keyPairsEquiv.symm (primaryEvent seed x y)]
  apply probability_le_of_update _ j
  intro K
  have hox (v : Chunk) : oh (keyPairsEquiv.symm (Function.update K j v)) x seed =
      xorChunk (phPrefix (keyPairsEquiv.symm K) xs) (enh v (lastChunk x) (blockTag seed x)) := by
    rw [oh_append_last _ x seed xs (lastChunk x) hxs,
      phPrefix_update_later K xs j le_rfl v, keyPair_of_pairs _ xs.length hn]
    simp [j]
  have hoy (v : Chunk) : oh (keyPairsEquiv.symm (Function.update K j v)) y seed =
      xorChunk (phPrefix (keyPairsEquiv.symm K) xs) (enh v (lastChunk x) (blockTag seed y)) := by
    rw [oh_append_last _ y seed xs (lastChunk x) hys,
      phPrefix_update_later K xs j le_rfl v, keyPair_of_pairs _ xs.length hn]
    simp [j]
  simp only [primaryEvent, hox, hoy]
  exact masked_enh_tag_probability (phPrefix (keyPairsEquiv.symm K) xs)
    (lastChunk x) (blockTag seed x) (blockTag seed y) hne (blockTag_common_high seed x y)
-- CHECKPOINT

/-- Lemma 6.2, including actual common PH masks and key conditioning. -/
theorem primary_tag_only_bound : PrimaryTagOnlyBound := by
  intro seed x y hx _hy hsame hne
  exact (primary_tag_only_le seed x y hx hsame hne).trans_lt (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
