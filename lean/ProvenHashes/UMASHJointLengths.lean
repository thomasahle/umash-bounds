import ProvenHashes.UMASHSecondaryLengths
import ProvenHashes.UMASHJointClosure

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem probability_or_le {K : Type*} [Fintype K] (E F : K → Prop) :
    uniformProb (fun k => E k ∨ F k) ≤ uniformProb E+uniformProb F := by
  classical
  have hset : @Finset.filter K (fun k => E k ∨ F k)
      (fun k => Classical.propDecidable (E k ∨ F k)) Finset.univ =
      (Finset.univ.filter E) ∪ (Finset.univ.filter F) := by ext k; simp
  unfold uniformProb
  rw [hset, ← add_div, ← Nat.cast_add]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_union_le _ _)) (by positivity)
-- CHECKPOINT

theorem joint_checksum_partition_bound (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16) :
    uniformProb (jointEvent seed x y) ≤
      uniformProb (fun k : OHKey => checksum k x = checksum k y)+
        uniformProb (primaryEvent seed x y)*((364816:ℚ≥0)/q) := by
  let P := fun K : Fin 17 → Chunk => primaryEvent seed x y (keyPairsEquiv.symm K)
  let C := fun K : Fin 17 → Chunk => checksum (keyPairsEquiv.symm K) x = checksum (keyPairsEquiv.symm K) y
  let E := fun K : Fin 17 → Chunk => P K ∧ ¬C K
  let F := fun K : Fin 17 → Chunk =>
    project (ohSecondary (keyPairsEquiv.symm K) x seed) = project (ohSecondary (keyPairsEquiv.symm K) y seed)
  have hE (K : Fin 17 → Chunk) (v : Chunk) : E (Function.update K 16 v) ↔ E K := by
    dsimp only [E, P, C, primaryEvent, oh]
    rw [mixed_update_later K x seed 16 hx v, mixed_update_later K y seed 16 hy v,
      checksum_update_later K x 16 hx v, checksum_update_later K y 16 hy v]
  have hprod := probability_and_update_event_le E F 16 ((364816:ℚ≥0)/q) hE
    (fun K hK => secondary_twist_different_checksum K seed x y hx hy hK.2)
  have hp : uniformProb E ≤ uniformProb P := probability_mono (fun _ h => h.1)
  have heqP : uniformProb P = uniformProb (primaryEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm (primaryEvent seed x y)
  have heqC : uniformProb C = uniformProb (fun k : OHKey => checksum k x = checksum k y) :=
    uniformProb_equiv keyPairsEquiv.symm (fun k => checksum k x = checksum k y)
  rw [← uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)]
  calc
    _ ≤ uniformProb (fun K => C K ∨ (E K ∧ F K)) := by
      apply probability_mono
      intro K hK
      by_cases hC : C K
      · exact Or.inl hC
      · exact Or.inr ⟨⟨hK.1,hC⟩,hK.2⟩
    _ ≤ uniformProb C+uniformProb (fun K => E K ∧ F K) := probability_or_le _ _
    _ ≤ uniformProb C+uniformProb P*((364816:ℚ≥0)/q) :=
      add_le_add_left (hprod.trans (mul_le_mul_of_nonneg_right hp (by positivity))) _
    _ = _ := by rw [heqP, heqC]
-- CHECKPOINT

theorem joint_different_chunk_counts_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : ¬sameCount x y) :
    uniformProb (jointEvent seed x y) ≤ (29914913:ℚ≥0)/q^2 := by
  have hxl : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hyl : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  have hcheck : uniformProb (fun k : OHKey => checksum k x = checksum k y) ≤ (1:ℚ≥0)/q^2 := by
    rcases lt_or_gt_of_ne hc with h | h
    · exact different_length_checksum_probability x y hy h
    · simpa only [eq_comm] using different_length_checksum_probability y x hx h
  calc
    _ ≤ uniformProb (fun k : OHKey => checksum k x = checksum k y)+
        uniformProb (primaryEvent seed x y)*((364816:ℚ≥0)/q) :=
      joint_checksum_partition_bound seed x y hxl hyl
    _ ≤ (1:ℚ≥0)/q^2+((82:ℚ≥0)/q)*((364816:ℚ≥0)/q) :=
      add_le_add hcheck (mul_le_mul_of_nonneg_right
        (corrected_different_chunk_counts_bound seed x y hx hy hc).le (by positivity))
    _ = _ := by ring
-- CHECKPOINT

theorem one_word_enh_bound : OneWordENHBound := by
  intro seed x y hx hy hc hp he
  have hne : lastChunk x ≠ lastChunk y := by
    intro h
    simp [enhChanges, h] at he
  exact (joint_enh_only_bound seed x y hx hy hc hp hne).trans_lt
    (by apply NNRat.coe_lt_coe.mp; norm_num [q])
-- CHECKPOINT

theorem closed_two_word_enh_bound : ClosedTwoWordENHBound := by
  intro seed x y hx hy hc hp he _hr
  have hne : lastChunk x ≠ lastChunk y := by
    intro h
    simp [enhChanges, h] at he
  exact (joint_enh_only_bound seed x y hx hy hc hp hne).trans_lt
    (by apply NNRat.coe_lt_coe.mp; norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
