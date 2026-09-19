import ProvenHashes.UMASHReferenceSwap
import ProvenHashes.UMASHAssembly

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

def minusOnePolyKey : PolyKey :=
  ⟨⟨p-1, by norm_num [p]⟩, by norm_num [p]⟩

/-- Exactly one allowed multiplier is p-1, independently of the distinct OH key. -/
theorem minus_one_multiplier_probability :
    uniformProb (fun k : Key64 => k.2 = minusOnePolyKey) = (1:ℚ≥0)/(p-2:ℕ) := by
  apply probability_prod_eq
  intro k
  simpa only [id_eq, polyKey_card] using
    probability_bijective_point (id : PolyKey → PolyKey) Function.bijective_id minusOnePolyKey
-- CHECKPOINT

/-- PROOF5 Proposition 11.1 is a lower bound for the excluded shared-multiplier
API. It makes no claim about the two independent multipliers in hash128. -/
theorem reference_swap_lower_bound : ReferenceSwapLowerBound := by
  intro seed
  rw [← minus_one_multiplier_probability]
  apply probability_mono
  intro k hk
  rcases k with ⟨ohKey,polyKey⟩
  change polyKey = minusOnePolyKey at hk
  subst polyKey
  exact reference_swap_collision ohKey.val seed
-- CHECKPOINT

end ProvenHashes.UMASH
