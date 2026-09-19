import ProvenHashes.UMASHENHPrimary
import ProvenHashes.UMASHENHPointMass

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

/-- Reindex the literal 34 IID words as their 17 independent pairs. -/
def keyPairsEquiv : OHKey ≃ (Fin 17 → Chunk) :=
  ((Equiv.arrowCongr (finProdFinEquiv (m := 17) (n := 2)).symm (Equiv.refl Word)).trans
    (Equiv.curry (Fin 17) (Fin 2) Word)).trans
      (Equiv.piCongrRight fun _ => finTwoArrowEquiv Word)

theorem keyPairsEquiv_apply (k : OHKey) (i : Fin 17) :
    keyPairsEquiv k i = keyPair k i.val := by
  change (k (finProdFinEquiv (n := 2) (i,0)), k (finProdFinEquiv (n := 2) (i,1))) = _
  simp only [keyPair, keyWord]
  apply Prod.ext
  all_goals
    apply congrArg k
    apply Fin.ext
    dsimp [finProdFinEquiv]
    have hi := i.isLt
    omega
-- CHECKPOINT

theorem keyPair_of_pairs (K : Fin 17 → Chunk) (i : ℕ) (hi : i < 17) :
    keyPair (keyPairsEquiv.symm K) i = K ⟨i,hi⟩ := by
  rw [← keyPairsEquiv_apply (keyPairsEquiv.symm K) ⟨i,hi⟩,
    Equiv.apply_symm_apply]
-- CHECKPOINT

def phPrefix (k : OHKey) (xs : List Chunk) : Chunk :=
  (xs.mapIdx (fun i x => ph (keyPair k i) x)).foldl xorChunk (0,0)

theorem oh_append_last (k : OHKey) (b : Block) (seed : Word)
    (xs : List Chunk) (last : Chunk) (hb : b.chunks = xs ++ [last]) :
    oh k b seed = xorChunk (phPrefix k xs)
      (enh (keyPair k xs.length) last (blockTag seed b)) := by
  have hm : mixed k b seed =
      xs.mapIdx (fun i x => ph (keyPair k i) x) ++
        [enh (keyPair k xs.length) last (blockTag seed b)] := by
    simp only [mixed, hb, List.mapIdx_append_one, List.length_append,
      List.length_singleton, Nat.lt_irrefl, ↓reduceIte]
    congr 1
    apply List.mapIdx_eq_mapIdx_iff.mpr
    intro i hi
    simp only [show i+1 < xs.length+1 from by omega, ↓reduceIte]
  simp only [oh, hm, List.foldl_append, List.foldl_cons, List.foldl_nil, phPrefix]
-- CHECKPOINT

theorem phPrefix_update_later (K : Fin 17 → Chunk) (xs : List Chunk)
    (j : Fin 17) (hxs : xs.length ≤ j.val) (v : Chunk) :
    phPrefix (keyPairsEquiv.symm (Function.update K j v)) xs =
      phPrefix (keyPairsEquiv.symm K) xs := by
  unfold phPrefix
  apply congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro i hi
  have hi17 : i < 17 := lt_of_lt_of_le hi (hxs.trans (Nat.le_of_lt j.isLt))
  have hij : (⟨i,hi17⟩ : Fin 17) ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    change i = j.val at hh
    omega
  rw [keyPair_of_pairs _ i hi17, keyPair_of_pairs _ i hi17,
    Function.update_of_ne hij]
-- CHECKPOINT

theorem block_chunks_split (b : Block) (hb : b.chunks ≠ []) :
    b.chunks = b.chunks.dropLast ++ [lastChunk b] := by
  have hlast : lastChunk b = b.chunks.getLast hb := by
    simp only [lastChunk, List.getLastD_eq_getLast?, List.getLast?_eq_getLast hb,
      Option.getD_some]
  rw [hlast]
  exact (List.dropLast_append_getLast hb).symm
-- CHECKPOINT

theorem phDiffCount_zero_prefix (x y : Block) (hc : sameCount x y)
    (hp : phDiffCount x y = 0) : x.chunks.dropLast = y.chunks.dropLast := by
  have hf : ∀ xy ∈ x.chunks.dropLast.zip y.chunks.dropLast, xy.1 = xy.2 := by
    have hn := List.length_eq_zero_iff.mp hp
    intro xy hxy
    simpa only [bne_iff_ne, not_not] using (List.filter_eq_nil_iff.mp hn) xy hxy
  apply List.ext_getElem
  · simp only [List.length_dropLast, show x.chunks.length = y.chunks.length from hc]
  · intro i hi hj
    have hz : i < (x.chunks.dropLast.zip y.chunks.dropLast).length := by
      rw [List.length_zip]
      exact lt_min hi hj
    have hh := hf _ (List.getElem_mem hz)
    simpa only [List.getElem_zip] using hh
-- CHECKPOINT

/-- Theorem 4.5 for the actual block hash and all 34 IID OH key words. -/
theorem primary_enh_only_bound : PrimaryENHOnlyBound := by
  intro seed x y hx hy hc hp hne
  have hxlen : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨h0,h256,hn⟩
    omega
  have hylen : 0 < y.chunks.length := by
    change x.chunks.length = y.chunks.length at hc
    omega
  have hnx : x.chunks ≠ [] := List.ne_nil_of_length_pos hxlen.1
  have hny : y.chunks ≠ [] := List.ne_nil_of_length_pos hylen
  have hpre := phDiffCount_zero_prefix x y hc hp
  let xs := x.chunks.dropLast
  have hxs : x.chunks = xs ++ [lastChunk x] := block_chunks_split x hnx
  have hys : y.chunks = xs ++ [lastChunk y] := by
    dsimp only [xs]
    rw [hpre]
    exact block_chunks_split y hny
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
      xorChunk (phPrefix (keyPairsEquiv.symm K) xs) (enh v (lastChunk y) (blockTag seed y)) := by
    rw [oh_append_last _ y seed xs (lastChunk y) hys,
      phPrefix_update_later K xs j le_rfl v, keyPair_of_pairs _ xs.length hn]
    simp [j]
  simp only [primaryEvent, hox, hoy]
  exact masked_enh_probability (lastChunk x) (lastChunk y)
    (phPrefix (keyPairsEquiv.symm K) xs) (blockTag seed x) (blockTag seed y) hne
-- CHECKPOINT

theorem mixed_update_later (K : Fin 17 → Chunk) (b : Block) (seed : Word)
    (j : Fin 17) (hb : b.chunks.length ≤ j.val) (v : Chunk) :
    mixed (keyPairsEquiv.symm (Function.update K j v)) b seed =
      mixed (keyPairsEquiv.symm K) b seed := by
  unfold mixed
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro i hi
  have hi17 : i < 17 := lt_of_lt_of_le hi (hb.trans (Nat.le_of_lt j.isLt))
  have hij : (⟨i,hi17⟩ : Fin 17) ≠ j := by
    intro h
    have hh : i = j.val := congrArg Fin.val h
    omega
  simp only [keyPair_of_pairs _ i hi17, Function.update_of_ne hij]
-- CHECKPOINT

/-- Expose the longer block's final pair, which is absent from the shorter block. -/
theorem different_chunk_counts_ordered (seed : Word) (x y : Block) (hy : y.Valid)
    (hlt : x.chunks.length < y.chunks.length) :
    uniformProb (primaryEvent seed x y) ≤ ((82*q-81 : ℕ) : ℚ≥0)/(q:ℚ≥0)^2 := by
  have hylen : 0 < y.chunks.length ∧ y.chunks.length ≤ 16 := by
    rcases hy with ⟨h0,h256,hn⟩
    omega
  let ys := y.chunks.dropLast
  have hys : y.chunks = ys ++ [lastChunk y] :=
    block_chunks_split y (List.ne_nil_of_length_pos hylen.1)
  have hlen : ys.length < 17 := by
    dsimp only [ys]
    rw [List.length_dropLast]
    omega
  let j : Fin 17 := ⟨ys.length,hlen⟩
  have hxj : x.chunks.length ≤ j.val := by
    dsimp only [j, ys]
    rw [List.length_dropLast]
    omega
  rw [← uniformProb_equiv keyPairsEquiv.symm (primaryEvent seed x y)]
  apply probability_le_of_update _ j
  intro K
  have hox (v : Chunk) : oh (keyPairsEquiv.symm (Function.update K j v)) x seed =
      oh (keyPairsEquiv.symm K) x seed :=
    congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
      (mixed_update_later K x seed j hxj v)
  have hoy (v : Chunk) : oh (keyPairsEquiv.symm (Function.update K j v)) y seed =
      xorChunk (phPrefix (keyPairsEquiv.symm K) ys) (enh v (lastChunk y) (blockTag seed y)) := by
    rw [oh_append_last _ y seed ys (lastChunk y) hys,
      phPrefix_update_later K ys j le_rfl v, keyPair_of_pairs _ ys.length hlen]
    simp [j]
  simp only [primaryEvent, hox, hoy]
  simpa only [eq_comm] using enh_projected_point_mass_data (blockTag seed y)
    (phPrefix (keyPairsEquiv.symm K) ys) (lastChunk y) (project (oh (keyPairsEquiv.symm K) x seed))
-- CHECKPOINT

theorem corrected_different_chunk_counts_bound : CorrectedDifferentChunkCountsBound := by
  intro seed x y hx hy hc
  have hn : x.chunks.length ≠ y.chunks.length := hc
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact (different_chunk_counts_ordered seed x y hy hlt).trans_lt (by norm_num [q])
  · have h := (different_chunk_counts_ordered seed y x hx hgt).trans_lt
      (show ((82*q-81 : ℕ) : ℚ≥0)/(q:ℚ≥0)^2 < (82:ℚ≥0)/q by norm_num [q])
    have hfun : primaryEvent seed y x = primaryEvent seed x y :=
      funext (fun _ => propext eq_comm)
    rw [hfun] at h
    exact h
-- CHECKPOINT

end ProvenHashes.UMASH
