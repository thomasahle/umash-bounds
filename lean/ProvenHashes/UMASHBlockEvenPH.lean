import ProvenHashes.UMASHEvenPHSlice
import ProvenHashes.UMASHCorrectedObligations

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul chunkCode

/-- The fixed-bit 604-squared estimate on the actual OH key space. -/
theorem even_ph_bound : EvenPHBound := by
  intro seed x y hx hy _hc hdiff hodd
  have hlenx : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hleny : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  obtain ⟨i,j,hij,hi,hj,hxy⟩ := exists_differing_ph x y hdiff
  have hxget : x.chunks.getD i.val (0,0) = x.chunks[i] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some]
    rfl
  have hyget : y.chunks.getD i.val (0,0) = y.chunks[j] := by
    rw [hij]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt, Option.getD_some]
    rfl
  have heven : ((x.chunks[i]).1 ^^^ (y.chunks[j]).1).toNat%2 = 0 ∧
      ((x.chunks[i]).2 ^^^ (y.chunks[j]).2).toNat%2 = 0 := by
    have hn : ¬(((x.chunks[i]).1 ^^^ (y.chunks[j]).1).toNat%2 = 1 ∨
        ((x.chunks[i]).2 ^^^ (y.chunks[j]).2).toNat%2 = 1) := by
      intro h
      apply hodd
      refine ⟨i.val, hi, ?_⟩
      simpa only [hxget, hyget] using h
    constructor <;> omega
  by_cases hfirst : (x.chunks[i]).1 ≠ (y.chunks[j]).1
  · apply probability_le_of_update (primaryEvent seed x y) (phKeyIndex i.val 1)
    intro k
    obtain ⟨M,hM⟩ := oh_update_ph_mask k x seed hlenx i hi 1
    obtain ⟨N,hN⟩ := oh_update_ph_mask k y seed hleny j hj 1
    have hN' (v : Word) : oh (Function.update k (phKeyIndex i.val 1) v) y seed =
        xorChunk N (ph (keyPair (Function.update k (phKeyIndex i.val 1) v) i.val) y.chunks[j]) := by
      simpa only [hij] using hN v
    have hk (v : Word) : keyPair (Function.update k (phKeyIndex i.val 1) v) i.val =
        (keyWord k (2*i.val),v) := by
      simpa only [Fin.val_one, one_ne_zero, ↓reduceIte] using
        keyPair_update_same k i.val 1 v (by have := i.isLt; omega)
    simp only [primaryEvent, hM, hN', hk]
    exact masked_ph_even_right_probability x.chunks[i] y.chunks[j] M N
      (keyWord k (2*i.val)) hfirst heven.1
  · have hsecond : (x.chunks[i]).2 ≠ (y.chunks[j]).2 := by
      intro h
      exact hxy (Prod.ext (not_ne_iff.mp hfirst) h)
    apply probability_le_of_update (primaryEvent seed x y) (phKeyIndex i.val 0)
    intro k
    obtain ⟨M,hM⟩ := oh_update_ph_mask k x seed hlenx i hi 0
    obtain ⟨N,hN⟩ := oh_update_ph_mask k y seed hleny j hj 0
    have hN' (v : Word) : oh (Function.update k (phKeyIndex i.val 0) v) y seed =
        xorChunk N (ph (keyPair (Function.update k (phKeyIndex i.val 0) v) i.val) y.chunks[j]) := by
      simpa only [hij] using hN v
    have hk (v : Word) : keyPair (Function.update k (phKeyIndex i.val 0) v) i.val =
        (v,keyWord k (2*i.val+1)) := by
      simpa only [Fin.val_zero, ↓reduceIte] using
        keyPair_update_same k i.val 0 v (by have := i.isLt; omega)
    simp only [primaryEvent, hM, hN', hk]
    exact masked_ph_even_left_probability x.chunks[i] y.chunks[j] M N
      (keyWord k (2*i.val+1)) hsecond heven.2
-- CHECKPOINT

end ProvenHashes.UMASH
