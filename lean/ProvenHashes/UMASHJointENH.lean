import ProvenHashes.UMASHBlockENH
import ProvenHashes.UMASHJointProbability

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul chunkCode

/-- A coarse two-lane PH projection bound with different fixed XOR offsets. -/
theorem masked_ph_probability (x y M N : Chunk) (hxy : x ≠ y) :
    uniformProb (fun k : Chunk => project (xorChunk M (ph k x)) =
      project (xorChunk N (ph k y))) ≤ (852:ℚ≥0)^2/q := by
  have hs (f g : Word → Chunk)
      (hi : Function.Injective (fun v => chunkCode (f v)+chunkCode (g v))) :
      uniformProb (fun v : Word => project (xorChunk M (f v)) =
        project (xorChunk N (g v))) ≤ (852:ℚ≥0)^2/q := by
    have hm : Function.Injective (fun v =>
        chunkCode (xorChunk M (f v))+chunkCode (xorChunk N (g v))) := by
      intro a b hab
      apply hi
      simp only [chunkCode_xor] at hab
      have hh := congrArg (fun z : ChunkCode => z-(chunkCode M+chunkCode N)) hab
      convert hh using 1 <;> abel
    simpa only [word_card] using projected_chunkCode_bound
      (fun v => xorChunk M (f v)) (fun v => xorChunk N (g v)) hm
  by_cases hx : x.1 ≠ y.1
  · apply probability_prod_le
    intro fixed
    exact hs _ _ (ph_code_slice_right x y hx fixed)
  · have hy : x.2 ≠ y.2 := fun h => hxy (Prod.ext (not_ne_iff.mp hx) h)
    rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => project (xorChunk M (ph k x)) = project (xorChunk N (ph k y)))]
    apply probability_prod_le
    intro fixed
    exact hs _ _ (ph_code_slice_left x y hy fixed)
-- CHECKPOINT

theorem checksum_append_last (k : OHKey) (b : Block) (xs : List Chunk) (last : Chunk)
    (hb : b.chunks = xs ++ [last]) :
    checksum k b = xorChunk (checksum k ⟨xs,0⟩) (xorChunk last (keyPair k xs.length)) := by
  simp only [checksum, hb, List.mapIdx_append_one, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
-- CHECKPOINT

theorem checksum_ne_of_last (k : OHKey) (x y : Block)
    (hx : x.chunks ≠ []) (hy : y.chunks ≠ [])
    (hp : x.chunks.dropLast = y.chunks.dropLast) (hne : lastChunk x ≠ lastChunk y) :
    checksum k x ≠ checksum k y := by
  intro he
  rw [checksum_append_last k x _ _ (block_chunks_split x hx),
    checksum_append_last k y _ _ (block_chunks_split y hy), ← hp] at he
  have hh := congrArg chunkCode he
  simp only [chunkCode_xor] at hh
  exact hne (chunkCode_injective (add_right_cancel (add_left_cancel hh)))
-- CHECKPOINT

theorem checksum_update_later (K : Fin 17 → Chunk) (b : Block)
    (j : Fin 17) (hb : b.chunks.length ≤ j.val) (v : Chunk) :
    checksum (keyPairsEquiv.symm (Function.update K j v)) b =
      checksum (keyPairsEquiv.symm K) b := by
  unfold checksum
  apply congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro i hi
  have hi17 : i < 17 := lt_of_lt_of_le hi (hb.trans (Nat.le_of_lt j.isLt))
  have hij : (⟨i,hi17⟩ : Fin 17) ≠ j := by
    intro h
    have hh : i = j.val := congrArg Fin.val h
    omega
  simp only [keyPair_of_pairs _ i hi17, Function.update_of_ne hij]
-- CHECKPOINT

def secondaryBody (k : OHKey) (b : Block) (seed : Word) : Chunk :=
  ((mixed k b seed).mapIdx (fun i v => shuffle v (i+1) b.chunks.length)).foldl
    xorChunk (0,0)

theorem ohSecondary_eq_body (k : OHKey) (b : Block) (seed : Word) :
    ohSecondary k b seed =
      xorChunk (secondaryBody k b seed) (ph (keyPair k 16) (checksum k b)) := by
  apply chunkCode_injective
  simp only [ohSecondary, secondaryBody, chunkCode_fold, chunkCode_xor,
    chunkCode_zero, zero_add]
  exact add_comm _ _
-- CHECKPOINT

theorem secondary_twist_slice (K : Fin 17 → Chunk) (b : Block) (seed : Word)
    (hb : b.chunks.length ≤ 16) (v : Chunk) :
    ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) b seed =
      xorChunk (secondaryBody (keyPairsEquiv.symm K) b seed)
        (ph v (checksum (keyPairsEquiv.symm K) b)) := by
  have hm : secondaryBody (keyPairsEquiv.symm (Function.update K 16 v)) b seed =
      secondaryBody (keyPairsEquiv.symm K) b seed := by
    dsimp only [secondaryBody]
    rw [mixed_update_later K b seed 16 hb v]
  rw [ohSecondary_eq_body, hm, checksum_update_later K b 16 hb v,
    keyPair_of_pairs _ 16 (by decide)]
  simp
-- CHECKPOINT

/-- A coarse joint bound sufficient to close OpenENHOnly.  This retains the
two-lane PH mask count; it is separate from the sharper requested 4721784/q². -/
theorem joint_enh_only_coarse_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y) (hp : phDiffCount x y = 0)
    (hne : lastChunk x ≠ lastChunk y) :
    uniformProb (jointEvent seed x y) ≤ (5542*852^2:ℚ≥0)/(q:ℚ≥0)^2 := by
  have hxlen : 0 < x.chunks.length ∧ x.chunks.length ≤ 16 := by
    rcases hx with ⟨h0,h256,hn⟩
    omega
  have hylen : 0 < y.chunks.length ∧ y.chunks.length ≤ 16 := by
    rcases hy with ⟨h0,h256,hn⟩
    omega
  have hpre := phDiffCount_zero_prefix x y hc hp
  let E := fun K : Fin 17 → Chunk => primaryEvent seed x y (keyPairsEquiv.symm K)
  let F := fun K : Fin 17 → Chunk =>
    project (ohSecondary (keyPairsEquiv.symm K) x seed) =
      project (ohSecondary (keyPairsEquiv.symm K) y seed)
  have hind (K : Fin 17 → Chunk) (v : Chunk) : E (Function.update K 16 v) ↔ E K := by
    have hox : oh (keyPairsEquiv.symm (Function.update K 16 v)) x seed =
        oh (keyPairsEquiv.symm K) x seed :=
      congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
        (mixed_update_later K x seed 16 hxlen.2 v)
    have hoy : oh (keyPairsEquiv.symm (Function.update K 16 v)) y seed =
        oh (keyPairsEquiv.symm K) y seed :=
      congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
        (mixed_update_later K y seed 16 hylen.2 v)
    dsimp only [E, primaryEvent]
    rw [hox, hoy]
  have hs (K : Fin 17 → Chunk) :
      uniformProb (fun v => F (Function.update K 16 v)) ≤ (852:ℚ≥0)^2/q := by
    have hcheck := checksum_ne_of_last (keyPairsEquiv.symm K) x y
      (List.ne_nil_of_length_pos hxlen.1) (List.ne_nil_of_length_pos hylen.1) hpre hne
    dsimp only [F]
    simp only [secondary_twist_slice K x seed hxlen.2, secondary_twist_slice K y seed hylen.2]
    exact masked_ph_probability (checksum (keyPairsEquiv.symm K) x)
      (checksum (keyPairsEquiv.symm K) y) (secondaryBody (keyPairsEquiv.symm K) x seed)
      (secondaryBody (keyPairsEquiv.symm K) y seed) hcheck
  have hprod := probability_and_update_le E F 16 ((852:ℚ≥0)^2/q) hind hs
  have hequiv : uniformProb E = uniformProb (primaryEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm _
  have hjoint : uniformProb (fun K => E K ∧ F K) = uniformProb (jointEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)
  rw [hequiv, hjoint] at hprod
  calc
    _ ≤ uniformProb (primaryEvent seed x y)*((852:ℚ≥0)^2/q) := hprod
    _ ≤ ((5542:ℚ≥0)/q)*((852:ℚ≥0)^2/q) :=
      mul_le_mul_of_nonneg_right (primary_enh_only_bound seed x y hx hy hc hp hne) (by positivity)
    _ = _ := by ring
-- CHECKPOINT

/-- Unconditional closure of the actual high-valuation ENH-only target. -/
theorem open_enh_only : OpenENHOnly := by
  intro seed x y hx hy hc hp he _hr _hr'
  have hne : lastChunk x ≠ lastChunk y := by
    intro hh
    simp [enhChanges, hh] at he
  exact (joint_enh_only_coarse_bound seed x y hx hy hc hp hne).trans_lt (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
