import ProvenHashes.UMASHShufflerFibres
import ProvenHashes.UMASHSinglePH

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul chunkCode

theorem secondaryBody_code_sum (k : OHKey) (b : Block) (seed : Word) :
    chunkCode (secondaryBody k b seed) = ∑ i : Fin b.chunks.length,
      chunkCode (shuffle
        (if i.val+1 < b.chunks.length then ph (keyPair k i.val) b.chunks[i]
          else enh (keyPair k i.val) b.chunks[i] (blockTag seed b))
        (i.val+1) b.chunks.length) := by
  have hl : (((mixed k b seed).mapIdx (fun i v => shuffle v (i+1) b.chunks.length)).map
      chunkCode) = List.ofFn (fun i : Fin b.chunks.length =>
        chunkCode (shuffle
          (if i.val+1 < b.chunks.length then ph (keyPair k i.val) b.chunks[i]
            else enh (keyPair k i.val) b.chunks[i] (blockTag seed b))
          (i.val+1) b.chunks.length)) := by
    apply List.ext_getElem
    · simp [mixed]
    · intro i hi hj
      simp [mixed]
  rw [secondaryBody, chunkCode_fold, chunkCode_zero, zero_add, hl, List.sum_ofFn]
-- CHECKPOINT

theorem secondaryBody_update_code_constant (k : OHKey) (b : Block) (seed : Word)
    (hlen : b.chunks.length ≤ 16) (i : Fin b.chunks.length)
    (hph : i.val+1 < b.chunks.length) (s : Fin 2) :
    ∃ C : ChunkCode, ∀ v : Word,
      chunkCode (secondaryBody (Function.update k (phKeyIndex i.val s) v) b seed) =
      chunkCode (shuffle
        (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val) b.chunks[i])
        (i.val+1) b.chunks.length) + C := by
  let f (k' : OHKey) (j : Fin b.chunks.length) : ChunkCode :=
    chunkCode (shuffle
      (if j.val+1 < b.chunks.length then ph (keyPair k' j.val) b.chunks[j]
        else enh (keyPair k' j.val) b.chunks[j] (blockTag seed b))
      (j.val+1) b.chunks.length)
  refine ⟨∑ j ∈ Finset.univ.erase i, f k j, ?_⟩
  intro v
  rw [secondaryBody_code_sum]
  change (∑ j, f (Function.update k (phKeyIndex i.val s) v) j) = _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  apply congrArg₂ (fun a b : ChunkCode => a+b)
  · simp only [f, hph, ↓reduceIte]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j.val ≠ i.val := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    have hk := keyPair_update_other k i.val j.val s v
      (by have := i.isLt; omega) (by have := j.isLt; omega) hji
    simp only [f, hk]
-- CHECKPOINT

theorem secondaryBody_update_ph_mask (k : OHKey) (b : Block) (seed : Word)
    (hlen : b.chunks.length ≤ 16) (i : Fin b.chunks.length)
    (hph : i.val+1 < b.chunks.length) (s : Fin 2) :
    ∃ M : Chunk, ∀ v : Word,
      secondaryBody (Function.update k (phKeyIndex i.val s) v) b seed =
      xorChunk M (shuffle
        (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val) b.chunks[i])
        (i.val+1) b.chunks.length) := by
  obtain ⟨C,hC⟩ := secondaryBody_update_code_constant k b seed hlen i hph s
  let p₀ := shuffle (ph (keyPair (Function.update k (phKeyIndex i.val s) 0) i.val)
    b.chunks[i]) (i.val+1) b.chunks.length
  let M := xorChunk (secondaryBody (Function.update k (phKeyIndex i.val s) 0) b seed) p₀
  have hself : chunkCode p₀+chunkCode p₀ = 0 := by
    rw [← chunkCode_xor]
    have hz : xorChunk p₀ p₀ = (0,0) := by simp [xorChunk]
    rw [hz, chunkCode_zero]
  have hM : chunkCode M = C := by
    dsimp only [M]
    rw [chunkCode_xor, hC 0]
    change (chunkCode p₀+C)+chunkCode p₀ = C
    calc
      _ = (chunkCode p₀+chunkCode p₀)+C := by abel
      _ = C := by rw [hself, zero_add]
  refine ⟨M, ?_⟩
  intro v
  apply chunkCode_injective
  rw [chunkCode_xor, hM, hC v]
  exact add_comm _ _
-- CHECKPOINT

theorem phShuffleWide_reference_difference (a b : Chunk) (i n : ℕ) (hi : i < n) :
    split (phShuffleWide (n-i) (join (xorChunk a b))) =
      xorChunk (shuffle a i n) (shuffle b i n) := by
  rw [shuffle_nonfinal_xor a b i n hi, phShuffleWide, split_join, split_join]
  rfl
-- CHECKPOINT

theorem ph_xor_join_top_bit (key key' x y : Chunk) :
    (join (xorChunk (ph key x) (ph key' y))).getLsbD 127 = false := by
  rw [ph, ph, ← split_xor, join_split]
  simp only [BitVec.getLsbD_xor, clmul_top_bit, Bool.xor_self]
-- CHECKPOINT

/-- Cancel the common twisting contribution before counting raw masks. -/
theorem xorChunk_twist_cancel (M N P Q T : Chunk) :
    xorChunk (xorChunk (xorChunk M P) T) (xorChunk (xorChunk N Q) T) =
      xorChunk (xorChunk P Q) (xorChunk M N) := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit _
  · simp only [xorChunk, BitVec.getLsbD_xor]
    cases M.1.getLsbD bit <;> cases N.1.getLsbD bit <;> cases P.1.getLsbD bit <;>
      cases Q.1.getLsbD bit <;> cases T.1.getLsbD bit <;> rfl
  · simp only [xorChunk, BitVec.getLsbD_xor]
    cases M.2.getLsbD bit <;> cases N.2.getLsbD bit <;> cases P.2.getLsbD bit <;>
      cases Q.2.getLsbD bit <;> cases T.2.getLsbD bit <;> rfl
-- CHECKPOINT

/-- PROOF5 Lemma 4.2 for literal blocks: equal checksums and a PH change
give the secondary marginal 2*604^2/q, even though the common checksum
value itself can depend on the exposed PH key. -/
theorem secondary_equal_checksum_ph_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hcheck : dataChecksum x = dataChecksum y) (hph : 0 < phDiffCount x y) :
    uniformProb (fun k : OHKey => project (ohSecondary k x seed) =
      project (ohSecondary k y seed)) ≤ (729632:ℚ≥0)/q := by
  have hlenx : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hleny : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  have hcount : x.chunks.length = y.chunks.length := hc
  obtain ⟨i,j,hij,hi,hj,hxy⟩ := exists_differing_ph x y hph
  obtain ⟨s,hs⟩ := ph_key_update_injective x.chunks[i] y.chunks[j] hxy i.val (by omega)
  apply probability_le_of_update _ (phKeyIndex i.val s)
  intro k
  obtain ⟨M,hM⟩ := secondaryBody_update_ph_mask k x seed hlenx i hi s
  obtain ⟨N,hN⟩ := secondaryBody_update_ph_mask k y seed hleny j hj s
  have hN' (v : Word) : secondaryBody (Function.update k (phKeyIndex i.val s) v) y seed =
      xorChunk N (shuffle
        (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val) y.chunks[j])
        (i.val+1) x.chunks.length) := by
    simpa only [← hij, ← hcount] using hN v
  let f (v : Word) : Wide := join (xorChunk
    (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val) x.chunks[i])
    (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val) y.chunks[j]))
  have hinj : Function.Injective f := by
    intro a b hab
    apply hs k
    have hh := congrArg (fun z : Wide => chunkCode (split z)) hab
    simpa only [f, split_join, chunkCode_xor] using hh
  have htop (v : Word) : (f v).getLsbD 127 = false := ph_xor_join_top_bit _ _ _ _
  have hraw (v : Word) :
      xorChunk (ohSecondary (Function.update k (phKeyIndex i.val s) v) x seed)
        (ohSecondary (Function.update k (phKeyIndex i.val s) v) y seed) =
      xorChunk (split (phShuffleWide (x.chunks.length-(i.val+1)) (f v))) (xorChunk M N) := by
    rw [ohSecondary_eq_body, ohSecondary_eq_body,
      checksum_eq_of_data_checksum _ x y hc hcheck, hM v, hN' v]
    dsimp only [f]
    rw [phShuffleWide_reference_difference _ _ _ _ hi]
    exact xorChunk_twist_cancel _ _ _ _ _
  simpa only [word_card] using shuffled_projected_collision_bound
    (fun v => ohSecondary (Function.update k (phKeyIndex i.val s) v) x seed)
    (fun v => ohSecondary (Function.update k (phKeyIndex i.val s) v) y seed)
    f (xorChunk M N) hinj htop (x.chunks.length-(i.val+1)) (by omega) hraw
-- CHECKPOINT

end ProvenHashes.UMASH
