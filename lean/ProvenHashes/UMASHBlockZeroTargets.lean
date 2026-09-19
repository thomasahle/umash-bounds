import ProvenHashes.UMASHTwistPoint
import ProvenHashes.UMASHLongIdentity

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem secondary_zero_slice_probability (K : Fin 17 → Chunk) (seed : Word) (b : Block)
    (hb : b.chunks.length ≤ 16) :
    uniformProb (fun v : Chunk =>
      project (ohSecondary (keyPairsEquiv.symm (Function.update K 16 v)) b seed) = (0,0)) ≤
      (297:ℚ≥0)/q := by
  simp only [secondary_twist_slice K b seed hb]
  apply (probability_mono ?_).trans
    (twist_low_field_point_probability (checksum (keyPairsEquiv.symm K) b)
      (secondaryBody (keyPairsEquiv.symm K) b seed).1 0)
  intro v hv
  exact congrArg Prod.fst hv
-- CHECKPOINT

theorem secondary_zero_probability (seed : Word) (b : Block) (hb : b.Valid) :
    uniformProb (fun k : OHKey => project (ohSecondary k b seed) = (0,0)) ≤ (297:ℚ≥0)/q := by
  have hbl : b.chunks.length ≤ 16 := by rcases hb with ⟨_,_,h⟩; omega
  rw [← uniformProb_equiv keyPairsEquiv.symm
    (fun k : OHKey => project (ohSecondary k b seed) = (0,0))]
  exact probability_le_of_update _ (16:Fin 17) _ (fun K => secondary_zero_slice_probability K seed b hbl)
-- CHECKPOINT

theorem joint_zero_probability (seed : Word) (b : Block) (hb : b.Valid) :
    uniformProb (fun k : OHKey => project (oh k b seed) = (0,0) ∧
      project (ohSecondary k b seed) = (0,0)) ≤ (24354:ℚ≥0)/q^2 := by
  have hbl : b.chunks.length ≤ 16 := by rcases hb with ⟨_,_,h⟩; omega
  let P := fun K : Fin 17 → Chunk => project (oh (keyPairsEquiv.symm K) b seed) = (0,0)
  let Q := fun K : Fin 17 → Chunk => project (ohSecondary (keyPairsEquiv.symm K) b seed) = (0,0)
  have hfix (K : Fin 17 → Chunk) (v : Chunk) : P (Function.update K 16 v) ↔ P K := by
    simp only [P,oh,mixed_update_later K b seed 16 hbl v]
  have hm := probability_and_update_le P Q 16 ((297:ℚ≥0)/q) hfix
    (fun K => secondary_zero_slice_probability K seed b hbl)
  have hp : uniformProb P ≤ (82:ℚ≥0)/q := by
    rw [uniformProb_equiv keyPairsEquiv.symm (fun k : OHKey => project (oh k b seed) = (0,0))]
    exact (block_zero_projection_probability seed b hb).le
  rw [← uniformProb_equiv keyPairsEquiv.symm
    (fun k : OHKey => project (oh k b seed) = (0,0) ∧ project (ohSecondary k b seed) = (0,0))]
  exact (hm.trans (mul_le_mul_of_nonneg_right hp (by positivity))).trans_eq (by ring)
-- CHECKPOINT

end ProvenHashes.UMASH
