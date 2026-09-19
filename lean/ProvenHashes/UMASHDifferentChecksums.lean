import ProvenHashes.UMASHSecondaryChecksum
import ProvenHashes.UMASHCorrectedBlock

/-! Independent twisting-key conditioning for the different-checksum row
of PROOF5. All probabilities are on the literal uniform OH key space. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul chunkCode

theorem joint_different_checksum_product (seed : Word) (x y : Block)
    (hx : x.chunks.length ≤ 16) (hy : y.chunks.length ≤ 16)
    (hne : ∀ k : OHKey, checksum k x ≠ checksum k y) :
    uniformProb (jointEvent seed x y) ≤
      uniformProb (primaryEvent seed x y)*((364816:ℚ≥0)/q) := by
  let E := fun K : Fin 17 → Chunk => primaryEvent seed x y (keyPairsEquiv.symm K)
  let F := fun K : Fin 17 → Chunk =>
    project (ohSecondary (keyPairsEquiv.symm K) x seed) =
      project (ohSecondary (keyPairsEquiv.symm K) y seed)
  have hind (K : Fin 17 → Chunk) (v : Chunk) : E (Function.update K 16 v) ↔ E K := by
    have hox := congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
      (mixed_update_later K x seed 16 hx v)
    have hoy := congrArg (fun l : List Chunk => l.foldl xorChunk (0,0))
      (mixed_update_later K y seed 16 hy v)
    change oh (keyPairsEquiv.symm (Function.update K 16 v)) x seed =
      oh (keyPairsEquiv.symm K) x seed at hox
    change oh (keyPairsEquiv.symm (Function.update K 16 v)) y seed =
      oh (keyPairsEquiv.symm K) y seed at hoy
    dsimp only [E, primaryEvent]
    rw [hox, hoy]
  have hs (K : Fin 17 → Chunk) :
      uniformProb (fun v => F (Function.update K 16 v)) ≤ (364816:ℚ≥0)/q :=
    secondary_twist_different_checksum K seed x y hx hy (hne _)
  have hprod := probability_and_update_le E F 16 ((364816:ℚ≥0)/q) hind hs
  have hequiv : uniformProb E = uniformProb (primaryEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm _
  have hjoint : uniformProb (fun K => E K ∧ F K) = uniformProb (jointEvent seed x y) :=
    uniformProb_equiv keyPairsEquiv.symm (jointEvent seed x y)
  rwa [hequiv, hjoint] at hprod
-- CHECKPOINT

theorem joint_different_data_checksum_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hne : dataChecksum x ≠ dataChecksum y) :
    uniformProb (jointEvent seed x y) ≤ (364816:ℚ≥0)^2/q^2 := by
  have hxl : x.chunks.length ≤ 16 := by rcases hx with ⟨_,_,h⟩; omega
  have hyl : y.chunks.length ≤ 16 := by rcases hy with ⟨_,_,h⟩; omega
  have hd : x.chunks ≠ y.chunks := by
    intro he
    exact hne (by simp only [dataChecksum, he])
  calc
    _ ≤ uniformProb (primaryEvent seed x y)*((364816:ℚ≥0)/q) :=
      joint_different_checksum_product seed x y hxl hyl
        (fun k he => hne ((checksum_eq_iff_data_checksum k x y hc).mp he))
    _ ≤ ((364816:ℚ≥0)/q)*((364816:ℚ≥0)/q) :=
      mul_le_mul_of_nonneg_right
        (corrected_primary_block_bound seed x y hx hy (Or.inl hd)) (by positivity)
    _ = _ := by ring
-- CHECKPOINT

theorem different_checksums_bound : DifferentChecksumsBound := by
  intro seed x y hx hy hc hne _hp
  exact (joint_different_data_checksum_bound seed x y hx hy hc hne).trans
    (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
