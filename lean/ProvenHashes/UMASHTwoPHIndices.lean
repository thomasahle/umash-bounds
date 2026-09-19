import ProvenHashes.UMASHSinglePH

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000

theorem list_filter_two_indices {α : Type*} (P : α → Bool) (xs : List α)
    (h : 2 ≤ (xs.filter P).length) :
    ∃ i j : Fin xs.length, i.val < j.val ∧ P xs[i] = true ∧ P xs[j] = true := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases ha : P a = true
    · have hp : 0 < (xs.filter P).length := by
        simp only [List.filter_cons, ha, ↓reduceIte, List.length_cons] at h
        omega
      obtain ⟨v,hv⟩ := List.exists_mem_of_length_pos hp
      have hm := List.mem_filter.mp hv
      obtain ⟨j,hj,he⟩ := List.getElem_of_mem hm.1
      refine ⟨⟨0, by simp⟩, ⟨j+1, by simpa using hj⟩, by simp, ha, ?_⟩
      change P xs[j] = true
      rw [he]
      exact hm.2
    · have ht : 2 ≤ (xs.filter P).length := by simpa [List.filter_cons, ha] using h
      obtain ⟨i,j,hij,hi,hj⟩ := ih ht
      exact ⟨i.succ,j.succ,by simpa using hij,by simpa using hi,by simpa using hj⟩
-- CHECKPOINT

theorem phDiffCount_two_indices (x y : Block) (hc : sameCount x y)
    (hp : 2 ≤ phDiffCount x y) :
    ∃ i j : ℕ, i < j ∧ j+1 < x.chunks.length ∧
      x.chunks.getD i (0,0) ≠ y.chunks.getD i (0,0) ∧
      x.chunks.getD j (0,0) ≠ y.chunks.getD j (0,0) := by
  let zs := x.chunks.dropLast.zip y.chunks.dropLast
  have hc' : x.chunks.length = y.chunks.length := hc
  have hzlen : zs.length = x.chunks.length-1 := by
    simp only [zs, List.length_zip, List.length_dropLast, ← hc', min_self]
  have hget (j : ℕ) (hj : j < zs.length) :
      zs[j] = (x.chunks.getD j (0,0), y.chunks.getD j (0,0)) := by
    have hxj : j < x.chunks.length := by omega
    have hyj : j < y.chunks.length := by omega
    simp only [zs, List.getElem_zip, List.getElem_dropLast, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hxj, List.getElem?_eq_getElem hyj, Option.getD_some]
  obtain ⟨i,j,hij,hi,hj⟩ := list_filter_two_indices (fun xy : Chunk × Chunk => xy.1 != xy.2) zs hp
  refine ⟨i.val,j.val,hij,by have := j.isLt; omega,?_,?_⟩
  · change (zs[i.val].1 != zs[i.val].2) = true at hi
    rw [hget i.val i.isLt] at hi
    simpa using hi
  · change (zs[j.val].1 != zs[j.val].2) = true at hj
    rw [hget j.val j.isLt] at hj
    simpa using hj
-- CHECKPOINT

end ProvenHashes.UMASH
