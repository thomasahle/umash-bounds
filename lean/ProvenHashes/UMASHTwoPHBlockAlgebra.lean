import ProvenHashes.UMASHSecondaryPH
import ProvenHashes.UMASHTwoPHShuffler

/-! Extracting two independent original PH key pairs from the literal
compressors. Constants retain all other chunk contributions and tags. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] ph clmul uniformProb chunkCode

def bodyMode (secondary : Bool) (k : OHKey) (b : Block) (seed : Word) : Chunk :=
  if secondary then secondaryBody k b seed else oh k b seed

def mixedMode (secondary : Bool) (n i : ℕ) (v : Chunk) : Chunk :=
  if secondary then shuffle v (i+1) n else v

theorem bodyMode_code_sum (secondary : Bool) (k : OHKey) (b : Block) (seed : Word) :
    chunkCode (bodyMode secondary k b seed) = ∑ i : Fin b.chunks.length,
      chunkCode (mixedMode secondary b.chunks.length i.val
        (if i.val+1 < b.chunks.length then ph (keyPair k i.val) b.chunks[i]
          else enh (keyPair k i.val) b.chunks[i] (blockTag seed b))) := by
  cases secondary
  · exact oh_code_sum k b seed
  · exact secondaryBody_code_sum k b seed
-- CHECKPOINT

theorem bodyMode_pair_code_constant (secondary : Bool) (K : Fin 17 → Chunk)
    (b : Block) (seed : Word) (hlen : b.chunks.length ≤ 16)
    (i : Fin b.chunks.length) (hph : i.val+1 < b.chunks.length) :
    ∃ C : ChunkCode, ∀ a : Chunk,
      chunkCode (bodyMode secondary
        (keyPairsEquiv.symm (Function.update K ⟨i.val, by omega⟩ a)) b seed) =
      chunkCode (mixedMode secondary b.chunks.length i.val (ph a b.chunks[i])) + C := by
  let ip : Fin 17 := ⟨i.val, by omega⟩
  let f (K' : Fin 17 → Chunk) (j : Fin b.chunks.length) : ChunkCode :=
    chunkCode (mixedMode secondary b.chunks.length j.val
      (if j.val+1 < b.chunks.length then
        ph (keyPair (keyPairsEquiv.symm K') j.val) b.chunks[j]
      else enh (keyPair (keyPairsEquiv.symm K') j.val) b.chunks[j] (blockTag seed b)))
  refine ⟨∑ j ∈ Finset.univ.erase i, f K j, ?_⟩
  intro a
  rw [bodyMode_code_sum]
  change (∑ j, f (Function.update K ip a) j) = _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  apply congrArg₂ (fun x y : ChunkCode => x+y)
  · simp only [f, hph, ↓reduceIte, keyPair_of_pairs _ i.val (by omega), ip, Function.update_self]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : (⟨j.val, by have := j.isLt; omega⟩ : Fin 17) ≠ ip := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (Fin.ext (congrArg (fun q : Fin 17 => q.val) he))
    simp only [f, keyPair_of_pairs _ j.val (by have := j.isLt; omega),
      Function.update_of_ne hji]
-- CHECKPOINT

theorem bodyMode_pair_update (secondary : Bool) (K : Fin 17 → Chunk)
    (b : Block) (seed : Word) (hlen : b.chunks.length ≤ 16)
    (i : Fin b.chunks.length) (hph : i.val+1 < b.chunks.length) (a : Chunk) :
    bodyMode secondary (keyPairsEquiv.symm (Function.update K ⟨i.val, by omega⟩ a)) b seed =
    xorChunk (bodyMode secondary (keyPairsEquiv.symm K) b seed)
      (xorChunk (mixedMode secondary b.chunks.length i.val (ph (K ⟨i.val, by omega⟩) b.chunks[i]))
        (mixedMode secondary b.chunks.length i.val (ph a b.chunks[i]))) := by
  obtain ⟨C,hC⟩ := bodyMode_pair_code_constant secondary K b seed hlen i hph
  have hK := hC (K ⟨i.val, by omega⟩)
  simp only [Function.update_eq_self] at hK
  apply chunkCode_injective
  rw [chunkCode_xor, chunkCode_xor, hK, hC]
  have hself (v : Chunk) : chunkCode v+chunkCode v = 0 := by
    rw [← chunkCode_xor]
    simpa only [xorChunk, BitVec.xor_self] using chunkCode_zero
  have rearrange (a b c : ChunkCode) : (a+c)+(a+b) = (a+a)+(b+c) := by abel
  rw [rearrange, hself, zero_add]
-- CHECKPOINT

theorem bodyMode_two_pair_mask (secondary : Bool) (K : Fin 17 → Chunk)
    (b : Block) (seed : Word) (hlen : b.chunks.length ≤ 16)
    (i j : Fin b.chunks.length) (hij : i ≠ j)
    (hi : i.val+1 < b.chunks.length) (hj : j.val+1 < b.chunks.length) :
    ∃ M : Chunk, ∀ a d : Chunk,
      bodyMode secondary (keyPairsEquiv.symm
        (Function.update (Function.update K ⟨i.val, by omega⟩ a) ⟨j.val, by omega⟩ d)) b seed =
      xorChunk (xorChunk (mixedMode secondary b.chunks.length i.val (ph a b.chunks[i]))
        (mixedMode secondary b.chunks.length j.val (ph d b.chunks[j]))) M := by
  let ip : Fin 17 := ⟨i.val, by omega⟩
  let jp : Fin 17 := ⟨j.val, by omega⟩
  have hji : jp ≠ ip := fun h => hij (Fin.ext (congrArg (fun q : Fin 17 => q.val) h).symm)
  refine ⟨xorChunk (bodyMode secondary (keyPairsEquiv.symm K) b seed)
    (xorChunk (mixedMode secondary b.chunks.length i.val (ph (K ip) b.chunks[i]))
      (mixedMode secondary b.chunks.length j.val (ph (K jp) b.chunks[j]))), ?_⟩
  intro a d
  rw [bodyMode_pair_update secondary _ b seed hlen j hj,
    bodyMode_pair_update secondary K b seed hlen i hi]
  have hk : (Function.update K ip a) jp = K jp := Function.update_of_ne hji _ _
  change xorChunk (xorChunk _ (xorChunk _ _)) (xorChunk
    (mixedMode secondary b.chunks.length j.val (ph ((Function.update K ip a) jp) b.chunks[j])) _) = _
  rw [hk]
  apply Prod.ext <;> simp only [xorChunk] <;> ac_rfl
-- CHECKPOINT

theorem mixedMode_phShuffle (n i : ℕ) (hi : i+1 < n) (v : Chunk) :
    mixedMode true n i v = phShuffleChunk (n-(i+1)) v := by
  have hs : n-(i+1) ≠ 0 := by omega
  simp only [mixedMode, Bool.true_eq, ↓reduceIte, shuffle, hs, phShuffleChunk,
    phShuffleLane, laneShift, xorChunk]
  split_ifs <;> apply Prod.ext <;> simp only <;> ac_rfl
-- CHECKPOINT

end ProvenHashes.UMASH
