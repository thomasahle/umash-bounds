import ProvenHashes.UMASHJointLedger

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] ph clmul maskSet uniformProb

/-- A singleton filtered list selects one position, even when the original
list has repeated values. -/
theorem list_filter_one_index {α : Type*} (P : α → Bool) (xs : List α)
    (h : (xs.filter P).length = 1) :
    ∃ i : Fin xs.length, P xs[i] = true ∧
      ∀ j : Fin xs.length, P xs[j] = true → j = i := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases ha : P a = true
    · have hz : xs.filter P = [] := by
        apply List.length_eq_zero_iff.mp
        simpa [List.filter_cons, ha] using h
      refine ⟨⟨0, by simp⟩, ha, ?_⟩
      intro j
      refine Fin.cases (fun _ => rfl) (fun k hk => ?_) j
      have hn := List.filter_eq_nil_iff.mp hz xs[k] (List.getElem_mem k.isLt)
      exact False.elim (hn (by simpa using hk))
    · have ht : (xs.filter P).length = 1 := by simpa [List.filter_cons, ha] using h
      obtain ⟨i, hi, hu⟩ := ih ht
      refine ⟨i.succ, ?_, ?_⟩
      · simpa using hi
      · intro j
        refine Fin.cases (fun hj => False.elim (ha (by simpa using hj))) (fun k hk => ?_) j
        exact congrArg Fin.succ (hu k (by simpa using hk))
-- CHECKPOINT

/-- The literal `phDiffCount = 1` identifies a unique changed nonfinal
position; every other nonfinal data chunk is equal. -/
theorem phDiffCount_one_index (x y : Block) (hc : sameCount x y)
    (hp : phDiffCount x y = 1) :
    ∃ i : ℕ, i+1 < x.chunks.length ∧
      x.chunks.getD i (0,0) ≠ y.chunks.getD i (0,0) ∧
      ∀ j : ℕ, j+1 < x.chunks.length → j ≠ i →
        x.chunks.getD j (0,0) = y.chunks.getD j (0,0) := by
  let zs := x.chunks.dropLast.zip y.chunks.dropLast
  have hc' : x.chunks.length = y.chunks.length := hc
  have hzlen : zs.length = x.chunks.length-1 := by
    simp only [zs, List.length_zip, List.length_dropLast, ← hc', min_self]
  have hget (j : ℕ) (hj : j < zs.length) :
      zs[j] = (x.chunks.getD j (0,0), y.chunks.getD j (0,0)) := by
    have hxj : j < x.chunks.length := by omega
    have hyj : j < y.chunks.length := by omega
    simp only [zs, List.getElem_zip, List.getElem_dropLast,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxj,
      List.getElem?_eq_getElem hyj, Option.getD_some]
  obtain ⟨i, hi, hu⟩ := list_filter_one_index (fun xy : Chunk × Chunk => xy.1 != xy.2) zs hp
  have hine : x.chunks.getD i.val (0,0) ≠ y.chunks.getD i.val (0,0) := by
    change (zs[i.val].1 != zs[i.val].2) = true at hi
    rw [hget i.val i.isLt] at hi
    simpa using hi
  refine ⟨i.val, by have := i.isLt; omega, hine, ?_⟩
  intro j hj hji
  by_contra hne
  have hjz : j < zs.length := by omega
  have hpred : (zs[j].1 != zs[j].2) = true := by
    rw [hget j hjz]
    simpa using hne
  have he := congrArg Fin.val (hu ⟨j,hjz⟩ hpred)
  exact hji he
-- CHECKPOINT

/-- Indexed XOR folds as finite sums, using total indexing so that the two
lists can have a common index type without dependent casts. -/
theorem chunkCode_mapIdx_sum (f : ℕ → Chunk → Chunk) (xs : List Chunk) :
    chunkCode ((xs.mapIdx f).foldl xorChunk (0,0)) =
      ∑ j : Fin xs.length, chunkCode (f j.val (xs.getD j.val (0,0))) := by
  have hl : (xs.mapIdx f).map chunkCode =
      List.ofFn (fun j : Fin xs.length => chunkCode (f j.val (xs.getD j.val (0,0)))) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      have hjx : j < xs.length := by simpa using hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjx]
  rw [chunkCode_fold, chunkCode_zero, zero_add, hl, List.sum_ofFn]
-- CHECKPOINT

/-- Every unchanged position cancels, for an arbitrary indexed chunk map. -/
theorem mapped_xor_single (f : ℕ → Chunk → Chunk) (xs ys : List Chunk)
    (hc : xs.length = ys.length) (i : ℕ) (hi : i < xs.length)
    (ho : ∀ j, j < xs.length → j ≠ i → xs.getD j (0,0) = ys.getD j (0,0)) :
    xorChunk ((xs.mapIdx f).foldl xorChunk (0,0))
      ((ys.mapIdx f).foldl xorChunk (0,0)) =
    xorChunk (f i (xs.getD i (0,0))) (f i (ys.getD i (0,0))) := by
  apply chunkCode_injective
  rw [chunkCode_xor, chunkCode_xor, chunkCode_mapIdx_sum, chunkCode_mapIdx_sum]
  have hs : (∑ j : Fin ys.length, chunkCode (f j.val (ys.getD j.val (0,0)))) =
      ∑ j : Fin xs.length, chunkCode (f j.val (ys.getD j.val (0,0))) := by rw [hc]
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_single (⟨i,hi⟩ : Fin xs.length)
  · intro j _ hji
    have hj : j.val ≠ i := fun h => hji (Fin.ext h)
    rw [ho j.val j.isLt hj, ← chunkCode_xor]
    simp only [xorChunk, BitVec.xor_self]
    exact chunkCode_zero
  · intro h
    exact False.elim (h (Finset.mem_univ _))
-- CHECKPOINT

/-- Apply single-position cancellation to the literal nonfinal prefix. -/
theorem nonfinal_mapped_xor_single (f : ℕ → Chunk → Chunk) (x y : Block)
    (hc : sameCount x y) (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) :
    xorChunk ((x.chunks.dropLast.mapIdx f).foldl xorChunk (0,0))
      ((y.chunks.dropLast.mapIdx f).foldl xorChunk (0,0)) =
    xorChunk (f i (x.chunks.getD i (0,0))) (f i (y.chunks.getD i (0,0))) := by
  have hc' : x.chunks.length = y.chunks.length := hc
  have hget (b : Block) (j : ℕ) (hj : j+1 < b.chunks.length) :
      b.chunks.dropLast.getD j (0,0) = b.chunks.getD j (0,0) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_dropLast,
      show j < b.chunks.length-1 from by omega, ↓reduceIte]
  have hh := mapped_xor_single f x.chunks.dropLast y.chunks.dropLast
    (by simp only [List.length_dropLast, hc']) i (by simp only [List.length_dropLast]; omega)
    (by
      intro j hj hji
      have hj' : j+1 < x.chunks.length := by simp only [List.length_dropLast] at hj; omega
      rw [hget x j hj', hget y j (by omega)]
      exact ho j hj' hji)
  simpa only [hget x i hi, hget y i (by omega)] using hh
-- CHECKPOINT

/-- PROOF2 equation (6), primary compressor, for the literal indexed loop. -/
theorem single_ph_primary_difference (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) :
    xorChunk (oh k x seed) (oh k y seed) =
      xorChunk
        (xorChunk (ph (keyPair k i) (x.chunks.getD i (0,0)))
          (ph (keyPair k i) (y.chunks.getD i (0,0))))
        (xorChunk (enh (keyPair k (x.chunks.length-1)) (lastChunk x) (blockTag seed x))
          (enh (keyPair k (x.chunks.length-1)) (lastChunk y) (blockTag seed y))) := by
  have hc' : x.chunks.length = y.chunks.length := hc
  have hx : x.chunks ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hy : y.chunks ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hprefix := nonfinal_mapped_xor_single (fun j d => ph (keyPair k j) d) x y hc i hi ho
  change xorChunk (phPrefix k x.chunks.dropLast) (phPrefix k y.chunks.dropLast) = _ at hprefix
  rw [oh_append_last k x seed _ _ (block_chunks_split x hx),
    oh_append_last k y seed _ _ (block_chunks_split y hy),
    List.length_dropLast, List.length_dropLast, ← hc']
  rw [← hprefix]
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j _ <;>
    simp [xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

/-- The reference nonfinal chunk shuffler acts on each lane by S_s,
including its special s=1 case, and commutes with XOR. -/
theorem shuffle_nonfinal_xor (a b : Chunk) (i n : ℕ) (hi : i < n) :
    xorChunk (shuffle a i n) (shuffle b i n) =
      (phShuffleLane (n-i) (a.1 ^^^ b.1), phShuffleLane (n-i) (a.2 ^^^ b.2)) := by
  have hs : n-i ≠ 0 := by omega
  unfold shuffle phShuffleLane
  simp only [hs, ↓reduceIte]
  split_ifs <;> apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j _ <;>
    simp [laneShift, xorChunk, BitVec.shiftLeft_xor_distrib,
      Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

/-- PROOF2 equation (6), secondary body. The same ENH difference remains,
while the one changed PH contribution receives its actual lane shuffler. -/
theorem single_ph_secondary_difference (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) :
    xorChunk (secondaryBody k x seed) (secondaryBody k y seed) =
      xorChunk
        (phShuffleLane (x.chunks.length-(i+1))
          ((ph (keyPair k i) (x.chunks.getD i (0,0))).1 ^^^
            (ph (keyPair k i) (y.chunks.getD i (0,0))).1),
         phShuffleLane (x.chunks.length-(i+1))
          ((ph (keyPair k i) (x.chunks.getD i (0,0))).2 ^^^
            (ph (keyPair k i) (y.chunks.getD i (0,0))).2))
        (xorChunk (enh (keyPair k (x.chunks.length-1)) (lastChunk x) (blockTag seed x))
          (enh (keyPair k (x.chunks.length-1)) (lastChunk y) (blockTag seed y))) := by
  have hc' : x.chunks.length = y.chunks.length := hc
  have hx : x.chunks ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hy : y.chunks ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hnx : x.chunks.dropLast.length+1 = x.chunks.length := by
    simp only [List.length_dropLast]; omega
  have hny : y.chunks.dropLast.length+1 = x.chunks.length := by
    simp only [List.length_dropLast]; omega
  have hprefix := nonfinal_mapped_xor_single
    (fun j d => shuffle (ph (keyPair k j) d) (j+1) x.chunks.length) x y hc i hi ho
  have hsx : (x.chunks.dropLast.mapIdx
      (fun j d => shuffle (ph (keyPair k j) d) (j+1) x.chunks.length)).foldl xorChunk (0,0) =
      secondaryPrefix k x.chunks.dropLast := by simp only [secondaryPrefix, hnx]
  have hsy : (y.chunks.dropLast.mapIdx
      (fun j d => shuffle (ph (keyPair k j) d) (j+1) x.chunks.length)).foldl xorChunk (0,0) =
      secondaryPrefix k y.chunks.dropLast := by simp only [secondaryPrefix, hny]
  rw [hsx, hsy, shuffle_nonfinal_xor _ _ _ _ hi] at hprefix
  rw [secondaryBody_append_last k x seed _ _ (block_chunks_split x hx),
    secondaryBody_append_last k y seed _ _ (block_chunks_split y hy),
    List.length_dropLast, List.length_dropLast, ← hc', ← hprefix]
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j _ <;>
    simp [xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

/-- Equal data checksums identify the selected PH input increments with
the final ENH input increments, coordinate by coordinate. -/
theorem single_ph_checksum_difference (x y : Block) (hc : sameCount x y)
    (hs : dataChecksum x = dataChecksum y) (i : ℕ) (hi : i+1 < x.chunks.length)
    (ho : ∀ j, j+1 < x.chunks.length → j ≠ i →
      x.chunks.getD j (0,0) = y.chunks.getD j (0,0)) :
    xorChunk (x.chunks.getD i (0,0)) (y.chunks.getD i (0,0)) =
      xorChunk (lastChunk x) (lastChunk y) := by
  have hc' : x.chunks.length = y.chunks.length := hc
  have hx : x.chunks ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hy : y.chunks ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hprefix := nonfinal_mapped_xor_single (fun _ d => d) x y hc i hi ho
  have hmap (zs : List Chunk) : zs.mapIdx (fun _ d => d) = zs := by
    apply List.ext_getElem <;> simp
  simp only [hmap] at hprefix
  rw [← hprefix]
  have hsplit (b : Block) (hb : b.chunks ≠ []) :
      dataChecksum b = xorChunk (b.chunks.dropLast.foldl xorChunk (0,0)) (lastChunk b) := by
    unfold dataChecksum
    conv_lhs => rw [block_chunks_split b hb]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hsplit x hx, hsplit y hy] at hs
  have hword (a b c d : Word) (he : a ^^^ c = b ^^^ d) : a ^^^ b = c ^^^ d := by
    apply BitVec.eq_of_getLsbD_eq
    intro j _
    have hb := congrArg (fun w : Word => w.getLsbD j) he
    simp only [BitVec.getLsbD_xor] at hb ⊢
    revert hb
    cases a.getLsbD j <;> cases b.getLsbD j <;>
      cases c.getLsbD j <;> cases d.getLsbD j <;> decide
  exact Prod.ext (hword _ _ _ _ (congrArg Prod.fst hs))
    (hword _ _ _ _ (congrArg Prod.snd hs))
-- CHECKPOINT

/-- With equal checksums the common twisting product cancels from the
secondary XOR difference, although its projected equality still depends on
both twisting words. -/
theorem secondary_difference_eq_body (k : OHKey) (seed : Word) (x y : Block)
    (hc : sameCount x y) (hs : dataChecksum x = dataChecksum y) :
    xorChunk (ohSecondary k x seed) (ohSecondary k y seed) =
      xorChunk (secondaryBody k x seed) (secondaryBody k y seed) := by
  rw [ohSecondary_eq_body, ohSecondary_eq_body, checksum_eq_of_data_checksum k x y hc hs]
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j _ <;>
    simp [xorChunk, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
-- CHECKPOINT

end ProvenHashes.UMASH
