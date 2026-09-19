import ProvenHashes.UMASHOddPHSlice
import ProvenHashes.UMASHBlockPH

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul chunkCode

theorem oh_update_ph_mask (k : OHKey) (b : Block) (seed : Word)
    (hlen : b.chunks.length ≤ 16) (i : Fin b.chunks.length)
    (hph : i.val+1 < b.chunks.length) (s : Fin 2) :
    ∃ M : Chunk, ∀ v : Word,
      oh (Function.update k (phKeyIndex i.val s) v) b seed =
        xorChunk M (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val) b.chunks[i]) := by
  obtain ⟨C,hC⟩ := oh_update_code_constant k b seed hlen i hph s
  let p₀ := ph (keyPair (Function.update k (phKeyIndex i.val s) 0) i.val) b.chunks[i]
  let M := xorChunk (oh (Function.update k (phKeyIndex i.val s) 0) b seed) p₀
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

theorem masked_ph_odd_right_probability (x y M N : Chunk) (fixed : Word)
    (hd : (x.1 ^^^ y.1).toNat%2 = 1) :
    uniformProb (fun k : Word => project (xorChunk M (ph (fixed,k) x)) =
      project (xorChunk N (ph (fixed,k) y))) ≤ (17:ℚ≥0)/q := by
  have hx : (x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed) = x.1 ^^^ y.1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  have ho : ((x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed)).getLsbD 0 = true := by
    rw [hx]
    change Nat.testBit (x.1 ^^^ y.1).toNat 0 = true
    simp only [Nat.testBit_zero, hd, decide_true]
  have hf (d mask : Chunk) (k : Word) :
      (xorChunk mask (ph (fixed,k) d)).1 = lowAffinePH (d.1 ^^^ fixed) d.2 mask.1 k := by
    simp only [xorChunk, ph, lowAffinePH]
    rw [BitVec.xor_comm k d.2]
  calc
    _ ≤ uniformProb (fun k : Word => (lowAffinePH (x.1 ^^^ fixed) x.2 M.1 k).toNat%p =
        (lowAffinePH (y.1 ^^^ fixed) y.2 N.1 k).toNat%p) := by
      apply probability_mono
      intro k hk
      have he := congrArg (fun z : Field × Field => z.1.val) hk
      simp only [project, ZMod.val_natCast] at he
      rw [hf x M k, hf y N k] at he
      exact he
    _ ≤ _ := odd_ph_low_probability (x.1 ^^^ fixed) (y.1 ^^^ fixed) x.2 y.2 M.1 N.1 ho
-- CHECKPOINT

theorem masked_ph_odd_left_probability (x y M N : Chunk) (fixed : Word)
    (hd : (x.2 ^^^ y.2).toNat%2 = 1) :
    uniformProb (fun k : Word => project (xorChunk M (ph (k,fixed) x)) =
      project (xorChunk N (ph (k,fixed) y))) ≤ (17:ℚ≥0)/q := by
  simpa only [ph, clmul_comm] using
    masked_ph_odd_right_probability (x.2,x.1) (y.2,y.1) M N fixed hd
-- CHECKPOINT

/-- Lemma 5.2 averaged over the actual OH key space. -/
theorem odd_ph_bound : OddPHBound := by
  intro seed x y hx hy hc ho
  obtain ⟨i,hi,ho⟩ := ho
  have hlenx : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hleny : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  have hiy : i+1 < y.chunks.length := by
    change x.chunks.length = y.chunks.length at hc
    omega
  have hix : i < x.chunks.length := by omega
  have hiy' : i < y.chunks.length := by omega
  have hxget : x.chunks.getD i (0,0) = x.chunks[i] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hix, Option.getD_some]
  have hyget : y.chunks.getD i (0,0) = y.chunks[i] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiy', Option.getD_some]
  rw [hxget, hyget] at ho
  rcases ho with ho | ho
  · apply probability_le_of_update (primaryEvent seed x y) (phKeyIndex i 1)
    intro k
    obtain ⟨M,hM⟩ := oh_update_ph_mask k x seed hlenx ⟨i,hix⟩ hi 1
    obtain ⟨N,hN⟩ := oh_update_ph_mask k y seed hleny ⟨i,hiy'⟩ hiy 1
    have hk (v : Word) : keyPair (Function.update k (phKeyIndex i 1) v) i =
        (keyWord k (2*i),v) := by
      simpa only [Fin.val_one, one_ne_zero, ↓reduceIte] using
        keyPair_update_same k i 1 v (by omega)
    simp only [primaryEvent, hM, hN, hk]
    exact masked_ph_odd_right_probability x.chunks[i] y.chunks[i] M N (keyWord k (2*i)) ho
  · apply probability_le_of_update (primaryEvent seed x y) (phKeyIndex i 0)
    intro k
    obtain ⟨M,hM⟩ := oh_update_ph_mask k x seed hlenx ⟨i,hix⟩ hi 0
    obtain ⟨N,hN⟩ := oh_update_ph_mask k y seed hleny ⟨i,hiy'⟩ hiy 0
    have hk (v : Word) : keyPair (Function.update k (phKeyIndex i 0) v) i =
        (v,keyWord k (2*i+1)) := by
      simpa only [Fin.val_zero, ↓reduceIte] using
        keyPair_update_same k i 0 v (by omega)
    simp only [primaryEvent, hM, hN, hk]
    exact masked_ph_odd_left_probability x.chunks[i] y.chunks[i] M N (keyWord k (2*i+1)) ho
-- CHECKPOINT

end ProvenHashes.UMASH
