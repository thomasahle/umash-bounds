import ProvenHashes.UMASHBlockPH
import ProvenHashes.UMASHKeyAcceptance

namespace ProvenHashes.UMASH
attribute [local irreducible] uniformProb ph clmul chunkCode

theorem injective_chunk_xor_point (x y : Word → Chunk) (t : Chunk)
    (hi : Function.Injective (fun k => chunkCode (x k)+chunkCode (y k))) :
    uniformProb (fun k => xorChunk (x k) (y k) = t) ≤ (1:ℚ≥0)/q := by
  have h := injective_target_probability _ hi {chunkCode t}
    (fun k => xorChunk (x k) (y k) = t) (fun k hk => ?_)
  · simpa only [Finset.card_singleton, Nat.cast_one, word_card] using h
  · apply Finset.mem_singleton.mpr
    simpa only [chunkCode_xor] using congrArg chunkCode hk
-- CHECKPOINT

/-- Lemma 5.1 for the literal PH loop: every full XOR target has probability
at most one over q for any two distinct data chunks. -/
theorem ph_xor_target_probability (x y t : Chunk) (hxy : x ≠ y) :
    uniformProb (fun k : Chunk => xorChunk (ph k x) (ph k y) = t) ≤ (1:ℚ≥0)/q := by
  by_cases hx : x.1 ≠ y.1
  · apply probability_prod_le
    intro fixed
    exact injective_chunk_xor_point _ _ t (ph_code_slice_right x y hx fixed)
  · have hy : x.2 ≠ y.2 := by
      intro hh
      exact hxy (Prod.ext (not_ne_iff.mp hx) hh)
    rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => xorChunk (ph k x) (ph k y) = t)]
    apply probability_prod_le
    intro fixed
    exact injective_chunk_xor_point _ _ t (ph_code_slice_left x y hy fixed)
-- CHECKPOINT

end ProvenHashes.UMASH
