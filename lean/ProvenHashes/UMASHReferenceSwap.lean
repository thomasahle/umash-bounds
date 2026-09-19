import ProvenHashes.UMASHContinuationObligations
import ProvenHashes.UMASHShortProbability
import ProvenHashes.UMASHAccumulator

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def referenceSwapZeroBlock : Block := ⟨List.replicate 16 (0,0), 256⟩
def referenceSwapOneBlock : Block :=
  ⟨List.replicate 16 (BitVec.ofNat 64 72340172838076673, BitVec.ofNat 64 72340172838076673), 256⟩

/-- Literal encoding of the two distinct, two-block messages in PROOF5 §11. -/
theorem referenceSwap_encoding :
    encode referenceSwapX = [referenceSwapZeroBlock, referenceSwapOneBlock] ∧
    encode referenceSwapY = [referenceSwapOneBlock, referenceSwapZeroBlock] ∧
    referenceSwapX.length = 512 ∧ referenceSwapY.length = 512 ∧ referenceSwapX ≠ referenceSwapY := by
  decide +kernel
-- CHECKPOINT

/-- At multiplier p-1 the implemented modulo-8p updates commute. -/
theorem polyStep_minus_one_commute (acc : ℕ) (x y : Chunk) :
    polyStep (p-1) (polyStep (p-1) acc x) y =
      polyStep (p-1) (polyStep (p-1) acc y) x := by
  have hsq : ((p-1)*(p-1))%p = 1 := by norm_num [p]
  simp only [polyStep, hsq, one_mul, Nat.add_assoc, Nat.mod_add_mod, Nat.add_mod_mod]
  congr 1
  omega
-- CHECKPOINT

theorem referenceSwap_hashWith (k : OHKey) (seed : Word) (secondary : Bool) :
    hashWith k (p-1) seed referenceSwapX secondary =
      hashWith k (p-1) seed referenceSwapY secondary := by
  obtain ⟨hx,hy,hlx,hly,_⟩ := referenceSwap_encoding
  simp only [hashWith, hlx, hly, show ¬512 ≤ 8 by decide, if_false,
    compress, hx, hy, List.map_cons, List.map_nil, polyReduce,
    List.foldl_cons, List.foldl_nil]
  rw [polyStep_minus_one_commute]
-- CHECKPOINT

theorem reference_swap_collision : ReferenceSwapCollision := by
  intro k seed
  exact Prod.ext (referenceSwap_hashWith k seed false) (referenceSwap_hashWith k seed true)
-- CHECKPOINT

end ProvenHashes.UMASH
