import ProvenHashes.UMASHPatterns

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 0
attribute [local irreducible] maskSet

def valuationMasks (r : ℕ) : Finset ℕ := maskSet.filter (fun d => d % 2^r = 0)
def patternWeight (r : ℕ) : ℕ := ∑ d ∈ valuationMasks r, (maskPatterns d).card

/-- Complete kernel evaluation of the finite mask-pattern table. -/
theorem patternWeight_table :
    patternWeight 0 = 2771 ∧ patternWeight 1 = 615 ∧
    patternWeight 2 = 127 ∧ patternWeight 3 = 3 ∧ patternWeight 4 = 1 := by
  unfold patternWeight valuationMasks
  rw [maskSet_eq_certificate]
  decide +kernel

end ProvenHashes.UMASH
