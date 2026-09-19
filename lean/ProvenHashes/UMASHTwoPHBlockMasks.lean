import ProvenHashes.UMASHTwoPHBlockAlgebra
import ProvenHashes.UMASHPHENHAlgebra

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] ph clmul uniformProb

theorem mixedMode_xor (secondary : Bool) (n i : ℕ) (hi : i+1 < n) (a b : Chunk) :
    mixedMode secondary n i (xorChunk a b) =
      xorChunk (mixedMode secondary n i a) (mixedMode secondary n i b) := by
  cases secondary
  · rfl
  · rw [mixedMode_phShuffle _ _ hi, mixedMode_phShuffle _ _ hi,
      mixedMode_phShuffle _ _ hi, phShuffleChunk_xor]
-- CHECKPOINT

theorem bodyMode_two_difference (secondary : Bool) (K : Fin 17 → Chunk)
    (seed : Word) (x y : Block) (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
    (i j : ℕ) (hij : i < j) (hj : j+1 < x.chunks.length) :
    ∃ C : Chunk, ∀ a b : Chunk,
      let K' := Function.update (Function.update K ⟨i, by omega⟩ a) ⟨j, by omega⟩ b
      xorChunk (bodyMode secondary (keyPairsEquiv.symm K') x seed)
        (bodyMode secondary (keyPairsEquiv.symm K') y seed) =
      xorChunk (xorChunk
        (mixedMode secondary x.chunks.length i
          (xorChunk (ph a (x.chunks.getD i (0,0))) (ph a (y.chunks.getD i (0,0)))))
        (mixedMode secondary x.chunks.length j
          (xorChunk (ph b (x.chunks.getD j (0,0))) (ph b (y.chunks.getD j (0,0)))))) C := by
  have hlen : x.chunks.length = y.chunks.length := hc
  have hy : y.chunks.length ≤ 16 := by omega
  have hi : i+1 < x.chunks.length := by omega
  let ix : Fin x.chunks.length := ⟨i, by omega⟩
  let jx : Fin x.chunks.length := ⟨j, by omega⟩
  let iy : Fin y.chunks.length := ⟨i, by omega⟩
  let jy : Fin y.chunks.length := ⟨j, by omega⟩
  obtain ⟨M,hM⟩ := bodyMode_two_pair_mask secondary K x seed hx ix jx
    (by intro h; have he := congrArg Fin.val h; change i = j at he; omega) hi hj
  obtain ⟨N,hN⟩ := bodyMode_two_pair_mask secondary K y seed hy iy jy
    (by intro h; have he := congrArg Fin.val h; change i = j at he; omega)
    (show i+1 < y.chunks.length by omega) (show j+1 < y.chunks.length by omega)
  refine ⟨xorChunk M N, ?_⟩
  intro a b
  dsimp only
  rw [hM a b, hN a b]
  simp only [mixedMode_xor _ _ _ hi, mixedMode_xor _ _ _ hj,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < x.chunks.length by omega),
    List.getElem?_eq_getElem (show j < x.chunks.length by omega),
    List.getElem?_eq_getElem (show i < y.chunks.length by omega),
    List.getElem?_eq_getElem (show j < y.chunks.length by omega), Option.getD_some,
    ix, jx, iy, jy, ← hlen]
  apply Prod.ext <;> simp only [xorChunk] <;> ac_rfl
-- CHECKPOINT

theorem two_ph_block_raw_masks (K : Fin 17 → Chunk) (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hc : sameCount x y)
    (i j : ℕ) (hij : i < j) (hj : j+1 < x.chunks.length) :
    ∃ C D : Chunk, ∀ a b : Chunk,
      let K' := Function.update (Function.update K ⟨i, by omega⟩ a) ⟨j, by omega⟩ b
      let A := xorChunk (ph a (x.chunks.getD i (0,0))) (ph a (y.chunks.getD i (0,0)))
      let B := xorChunk (ph b (x.chunks.getD j (0,0))) (ph b (y.chunks.getD j (0,0)))
      rawPrimaryMask (keyPairsEquiv.symm K') seed x y = xorChunk (xorChunk A B) C ∧
      rawSecondaryMask (keyPairsEquiv.symm K') seed x y =
        xorChunk (xorChunk (phShuffleChunk (x.chunks.length-(i+1)) A)
          (phShuffleChunk (x.chunks.length-(j+1)) B)) D := by
  obtain ⟨C,hC⟩ := bodyMode_two_difference false K seed x y hx hc i j hij hj
  obtain ⟨D,hD⟩ := bodyMode_two_difference true K seed x y hx hc i j hij hj
  refine ⟨C,D,?_⟩
  intro a b
  exact ⟨hC a b, by simpa only [bodyMode, ↓reduceIte,
    mixedMode_phShuffle _ _ (show i+1 < x.chunks.length by omega),
    mixedMode_phShuffle _ _ hj] using hD a b⟩
-- CHECKPOINT

end ProvenHashes.UMASH
