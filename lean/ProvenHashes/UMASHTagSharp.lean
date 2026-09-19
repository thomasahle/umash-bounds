import ProvenHashes.UMASHTagSharpCount
import ProvenHashes.UMASHSharpObligations

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem masked_enh_tag_sharp (M data : Chunk) (tag tag' : Word)
    (hne : tag ≠ tag') (hcommon : tag.toNat/256 = tag'.toNat/256) :
    uniformProb (fun k : Chunk => project (xorChunk M (enh k data tag)) =
      project (xorChunk M (enh k data tag'))) ≤ ((4096*8192*(2^36-1):ℕ):ℚ≥0)/q^2 := by
  have hzero : uniformProb (fun k : Chunk => project (xorChunk M (enh k (0,0) tag)) =
      project (xorChunk M (enh k (0,0) tag'))) ≤ ((4096*8192*(2^36-1):ℕ):ℚ≥0)/q^2 := by
    rcases le_total tag.toNat tag'.toNat with hle | hle
    · exact masked_enh_tag_sharp_ordered M tag tag' hne hle hcommon
    · have h := masked_enh_tag_sharp_ordered M tag' tag hne.symm hle hcommon.symm
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

theorem primary_tag_only_sharp_le (seed : Word) (x y : Block) (hx : x.Valid)
    (hsame : x.chunks = y.chunks) (hne : blockTag seed x ≠ blockTag seed y) :
    uniformProb (primaryEvent seed x y) ≤ ((4096*8192*(2^36-1):ℕ):ℚ≥0)/q^2 := by
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
  exact masked_enh_tag_sharp (phPrefix (keyPairsEquiv.symm K) xs)
    (lastChunk x) (blockTag seed x) (blockTag seed y) hne (blockTag_common_high seed x y)
-- CHECKPOINT

/-- PROOF2 Theorem 9.2: the independent primary tag-only strict bound. -/
theorem primary_tag_only_sharp : PrimaryTagOnlyBoundSharp := by
  intro seed x y hx _hy hsame hne
  exact (primary_tag_only_sharp_le seed x y hx hsame hne).trans_lt (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
