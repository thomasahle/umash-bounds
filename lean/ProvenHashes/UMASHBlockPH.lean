import ProvenHashes.UMASHRank
import ProvenHashes.UMASHMixture

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] clmul

abbrev ChunkCode := Polynomial (ZMod 2) × Polynomial (ZMod 2)
noncomputable def chunkCode (x : Chunk) : ChunkCode :=
  (bitPolynomial x.1, bitPolynomial x.2)

theorem chunkCode_injective : Function.Injective chunkCode := by
  intro a b h
  exact Prod.ext (bitPolynomial_injective (congrArg Prod.fst h))
    (bitPolynomial_injective (congrArg Prod.snd h))
-- CHECKPOINT

theorem chunkCode_zero : chunkCode (0, 0) = 0 := by
  exact Prod.ext (bitPolynomial_zero 64) (bitPolynomial_zero 64)
-- CHECKPOINT

theorem chunkCode_xor (a b : Chunk) :
    chunkCode (xorChunk a b) = chunkCode a + chunkCode b := by
  exact Prod.ext (bitPolynomial_xor a.1 b.1) (bitPolynomial_xor a.2 b.2)
-- CHECKPOINT

theorem chunkCode_fold (xs : List Chunk) (a : Chunk) :
    chunkCode (xs.foldl xorChunk a) = chunkCode a + (xs.map chunkCode).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, chunkCode_xor, List.map_cons, List.sum_cons]
    exact add_assoc _ _ _
-- CHECKPOINT

theorem oh_code_sum (k : OHKey) (b : Block) (seed : Word) :
    chunkCode (oh k b seed) = ∑ i : Fin b.chunks.length,
      chunkCode (if i.val+1 < b.chunks.length then ph (keyPair k i.val) b.chunks[i]
        else enh (keyPair k i.val) b.chunks[i] (blockTag seed b)) := by
  have hl : (mixed k b seed).map chunkCode = List.ofFn (fun i : Fin b.chunks.length =>
      chunkCode (if i.val+1 < b.chunks.length then ph (keyPair k i.val) b.chunks[i]
        else enh (keyPair k i.val) b.chunks[i] (blockTag seed b))) := by
    apply List.ext_getElem
    · simp [mixed]
    · intro i hi hj
      simp [mixed]
  rw [oh, chunkCode_fold, chunkCode_zero, zero_add, hl, List.sum_ofFn]
-- CHECKPOINT

theorem probability_prod_le {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (E : A × B → Prop) (bound : ℚ≥0)
    (hs : ∀ a, uniformProb (fun b => E (a,b)) ≤ bound) : uniformProb E ≤ bound := by
  classical
  have hc : (Fintype.card A : ℚ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [probability_prod]
  calc
    _ ≤ (∑ _a : A, bound) / Fintype.card A := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum (fun a _ => hs a)
    _ = bound := by simp [hc]
-- CHECKPOINT

/-- Exact averaging over a free key coordinate; all other coordinates are fixed. -/
theorem probability_le_of_update {I V : Type*} [Fintype I] [Fintype V]
    [Nonempty V] [DecidableEq I] (E : (I → V) → Prop) (i : I) (bound : ℚ≥0)
    (hs : ∀ k, uniformProb (fun v => E (Function.update k i v)) ≤ bound) :
    uniformProb E ≤ bound := by
  classical
  let e := (Equiv.funSplitAt i V).trans (Equiv.prodComm _ _)
  let v₀ : V := Classical.choice inferInstance
  have hu (r : {j // j ≠ i} → V) (v : V) :
      e.symm (r,v) = Function.update (e.symm (r,v₀)) i v := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e]
    · simp [e, Function.update, hj]
  rw [← uniformProb_equiv e.symm E]
  apply probability_prod_le
  intro r
  have heq : (fun v => E (e.symm (r,v))) =
      (fun v => E (Function.update (e.symm (r,v₀)) i v)) :=
    funext (fun v => congrArg E (hu r v))
  rw [heq]
  exact hs (e.symm (r,v₀))
-- CHECKPOINT

def phKeyIndex (i : ℕ) (s : Fin 2) : Fin 34 :=
  ⟨(2*i+s.val)%34, Nat.mod_lt _ (by decide)⟩

theorem phKeyIndex_val (i : ℕ) (s : Fin 2) (hi : i < 16) :
    (phKeyIndex i s).val = 2*i+s.val := by
  apply Nat.mod_eq_of_lt
  have := s.isLt
  omega
-- CHECKPOINT

theorem keyWord_update (k : OHKey) (r : Fin 34) (v : Word) (j : ℕ) (hj : j < 34) :
    keyWord (Function.update k r v) j = if j = r.val then v else keyWord k j := by
  simp [keyWord, Nat.mod_eq_of_lt hj, Function.update_apply, Fin.ext_iff]
-- CHECKPOINT

theorem keyPair_update_other (k : OHKey) (i j : ℕ) (s : Fin 2) (v : Word)
    (hi : i < 16) (hj : j < 16) (hji : j ≠ i) :
    keyPair (Function.update k (phKeyIndex i s) v) j = keyPair k j := by
  have hs := s.isLt
  have h0 : 2*j ≠ (phKeyIndex i s).val := by rw [phKeyIndex_val i s hi]; omega
  have h1 : 2*j+1 ≠ (phKeyIndex i s).val := by rw [phKeyIndex_val i s hi]; omega
  simp only [keyPair, keyWord_update k _ v (2*j) (by omega),
    keyWord_update k _ v (2*j+1) (by omega), h0, h1, ↓reduceIte]
-- CHECKPOINT

theorem keyPair_update_same (k : OHKey) (i : ℕ) (s : Fin 2) (v : Word) (hi : i < 16) :
    keyPair (Function.update k (phKeyIndex i s) v) i =
      if s.val = 0 then (v, keyWord k (2*i+1)) else (keyWord k (2*i), v) := by
  have hs := s.isLt
  rw [keyPair, keyWord_update k _ v (2*i) (by omega),
    keyWord_update k _ v (2*i+1) (by omega), phKeyIndex_val i s hi]
  by_cases h0 : s.val = 0
  · simp [h0, show 2*i+1 ≠ 2*i by omega]
  · have h1 : s.val = 1 := by omega
    simp [h1, show 2*i ≠ 2*i+1 by omega]
-- CHECKPOINT

attribute [local irreducible] chunkCode ph enh oh keyPair

/-- All other chunks, including the final ENH chunk, are constant on a PH key slice. -/
theorem oh_update_code_constant (k : OHKey) (b : Block) (seed : Word)
    (hlen : b.chunks.length ≤ 16) (i : Fin b.chunks.length)
    (hph : i.val+1 < b.chunks.length) (s : Fin 2) :
    ∃ C : ChunkCode, ∀ v : Word,
      chunkCode (oh (Function.update k (phKeyIndex i.val s) v) b seed) =
      chunkCode (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val)
        b.chunks[i]) + C := by
  classical
  let f (k' : OHKey) (j : Fin b.chunks.length) : ChunkCode :=
    chunkCode (if j.val+1 < b.chunks.length then ph (keyPair k' j.val) b.chunks[j]
      else enh (keyPair k' j.val) b.chunks[j] (blockTag seed b))
  refine ⟨∑ j ∈ Finset.univ.erase i, f k j, ?_⟩
  intro v
  rw [oh_code_sum]
  change (∑ j, f (Function.update k (phKeyIndex i.val s) v) j) = _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  apply congrArg₂ (fun a b : ChunkCode => a+b)
  · simp only [f, hph, ↓reduceIte]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j.val ≠ i.val := fun h =>
      (Finset.mem_erase.mp hj).1 (Fin.ext h)
    have hk := keyPair_update_other k i.val j.val s v
      (by have := i.isLt; omega) (by have := j.isLt; omega) hji
    simp only [f, hk]
-- CHECKPOINT

theorem ph_code_slice_right (x y : Chunk) (hxy : x.1 ≠ y.1) (fixed : Word) :
    Function.Injective (fun v : Word =>
      chunkCode (ph (fixed,v) x) + chunkCode (ph (fixed,v) y)) := by
  intro a b hab
  have hraw : clmul (x.1 ^^^ fixed) (x.2 ^^^ a) ^^^ clmul (y.1 ^^^ fixed) (y.2 ^^^ a) =
      clmul (x.1 ^^^ fixed) (x.2 ^^^ b) ^^^ clmul (y.1 ^^^ fixed) (y.2 ^^^ b) := by
    apply split_injective
    apply chunkCode_injective
    simpa only [split_xor, chunkCode_xor, ph] using hab
  have he (v : Word) :
      clmul (x.1 ^^^ fixed) (x.2 ^^^ v) ^^^ clmul (y.1 ^^^ fixed) (y.2 ^^^ v) =
      clmul ((x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed)) v ^^^
        (clmul (x.1 ^^^ fixed) x.2 ^^^ clmul (y.1 ^^^ fixed) y.2) := by
    rw [clmul_xor_right (x.1 ^^^ fixed) x.2 v,
      clmul_xor_right (y.1 ^^^ fixed) y.2 v,
      clmul_xor_left (x.1 ^^^ fixed) (y.1 ^^^ fixed) v]
    apply BitVec.eq_of_getLsbD_eq
    intro n _
    simp only [BitVec.getLsbD_xor, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]
  rw [he a, he b, BitVec.xor_left_inj] at hraw
  apply clmul_left_injective (d := (x.1 ^^^ fixed) ^^^ (y.1 ^^^ fixed)) _ hraw
  intro hz
  exact hxy ((BitVec.xor_left_inj fixed).mp (BitVec.xor_eq_zero_iff.mp hz))
-- CHECKPOINT

theorem ph_code_slice_left (x y : Chunk) (hxy : x.2 ≠ y.2) (fixed : Word) :
    Function.Injective (fun v : Word =>
      chunkCode (ph (v,fixed) x) + chunkCode (ph (v,fixed) y)) := by
  intro a b hab
  have hswap (z : Chunk) (v : Word) : ph (v,fixed) z = ph (fixed,v) (z.2,z.1) := by
    simp only [ph, clmul_comm]
  dsimp only at hab
  rw [hswap x a, hswap y a, hswap x b, hswap y b] at hab
  exact ph_code_slice_right (x.2,x.1) (y.2,y.1) hxy fixed hab
-- CHECKPOINT

theorem ph_key_update_injective (x y : Chunk) (hxy : x ≠ y) (i : ℕ) (hi : i < 16) :
    ∃ s : Fin 2, ∀ k : OHKey, Function.Injective (fun v : Word =>
      chunkCode (ph (keyPair (Function.update k (phKeyIndex i s) v) i) x) +
      chunkCode (ph (keyPair (Function.update k (phKeyIndex i s) v) i) y)) := by
  by_cases hx : x.1 = y.1
  · have hy : x.2 ≠ y.2 := fun h => hxy (Prod.ext hx h)
    refine ⟨0, ?_⟩
    intro k
    have hs (v : Word) := keyPair_update_same k i (0 : Fin 2) v hi
    simpa only [hs, Fin.val_zero, ↓reduceIte] using
      ph_code_slice_left x y hy (keyWord k (2*i+1))
  · refine ⟨1, ?_⟩
    intro k
    have hs (v : Word) := keyPair_update_same k i (1 : Fin 2) v hi
    simpa only [hs, Fin.val_one, one_ne_zero, ↓reduceIte] using
      ph_code_slice_right x y hx (keyWord k (2*i))
-- CHECKPOINT

theorem projected_chunkCode_bound {K : Type*} [Fintype K] (x y : K → Chunk)
    (hinj : Function.Injective (fun k => chunkCode (x k) + chunkCode (y k))) :
    uniformProb (fun k => project (x k) = project (y k)) ≤
      (852 : ℚ≥0)^2 / (Fintype.card K : ℚ≥0) := by
  apply projected_collision_mask_bound
  intro a b hab
  apply hinj
  have he : xorChunk (x a) (y a) = xorChunk (x b) (y b) := by
    apply Prod.ext
    · apply BitVec.eq_of_toNat_eq
      simpa only [xorChunk, BitVec.toNat_xor] using congrArg Prod.fst hab
    · apply BitVec.eq_of_toNat_eq
      simpa only [xorChunk, BitVec.toNat_xor] using congrArg Prod.snd hab
  simpa only [chunkCode_xor] using congrArg chunkCode he
-- CHECKPOINT

theorem exists_differing_ph (x y : Block) (h : 0 < phDiffCount x y) :
    ∃ (i : Fin x.chunks.length) (j : Fin y.chunks.length),
      i.val = j.val ∧ i.val+1 < x.chunks.length ∧ j.val+1 < y.chunks.length ∧
      x.chunks[i] ≠ y.chunks[j] := by
  obtain ⟨xy, hxy⟩ := List.length_pos_iff_exists_mem.mp h
  obtain ⟨hm, hn⟩ := List.mem_filter.mp hxy
  have hne : xy.1 ≠ xy.2 := by simpa using hn
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hm
  have hil : i+1 < x.chunks.length ∧ i+1 < y.chunks.length := by
    simp only [List.length_zip, List.length_dropLast] at hi
    omega
  refine ⟨⟨i, by omega⟩, ⟨i, by omega⟩, rfl, hil.1, hil.2, ?_⟩
  simp only [List.getElem_zip, List.getElem_dropLast] at hget
  simpa only [← hget] using hne
-- CHECKPOINT

/-- The paper's 852²/q bound for a block with a differing PH chunk,
averaged over all 34 independent, uniformly sampled key words. -/
theorem primary_ph_bound : PrimaryPHBound := by
  intro seed x y hx hy _hcount hdiff
  have hlenx : x.chunks.length ≤ 16 := by rcases hx with ⟨_, _, h⟩; omega
  have hleny : y.chunks.length ≤ 16 := by rcases hy with ⟨_, _, h⟩; omega
  obtain ⟨i, j, hij, hi, hj, hxy⟩ := exists_differing_ph x y hdiff
  obtain ⟨s, hs⟩ := ph_key_update_injective x.chunks[i] y.chunks[j] hxy i.val (by omega)
  apply probability_le_of_update (primaryEvent seed x y) (phKeyIndex i.val s)
  intro k
  obtain ⟨C, hC⟩ := oh_update_code_constant k x seed hlenx i hi s
  obtain ⟨D, hD⟩ := oh_update_code_constant k y seed hleny j hj s
  have hD' (v : Word) :
      chunkCode (oh (Function.update k (phKeyIndex i.val s) v) y seed) =
      chunkCode (ph (keyPair (Function.update k (phKeyIndex i.val s) v) i.val)
        y.chunks[j]) + D := by simpa only [hij] using hD v
  have hinj : Function.Injective (fun v : Word =>
      chunkCode (oh (Function.update k (phKeyIndex i.val s) v) x seed) +
      chunkCode (oh (Function.update k (phKeyIndex i.val s) v) y seed)) := by
    intro a b hab
    dsimp only at hab
    rw [hC a, hD' a, hC b, hD' b] at hab
    apply hs k
    dsimp only
    have ht := congrArg (fun z : ChunkCode => z-(C+D)) hab
    convert ht using 1 <;> abel
  have hw : Fintype.card Word = q :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin q)
  simpa only [primaryEvent, hw] using projected_chunkCode_bound
    (fun v => oh (Function.update k (phKeyIndex i.val s) v) x seed)
    (fun v => oh (Function.update k (phKeyIndex i.val s) v) y seed) hinj
-- CHECKPOINT

end ProvenHashes.UMASH
