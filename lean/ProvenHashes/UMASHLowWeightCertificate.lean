import ProvenHashes.UMASHTwistPopcount
import ProvenHashes.UMASHMaskCensus3125

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] maskSet

/-- Exact finite sums of the popcount envelope, evaluated using the sorted
mask representation to avoid repeated quadratic deduplication. -/
theorem twist_low_popcount_sum_certificate :
    (∑ v ∈ valuationMasks 1, twistLowPopcountWeight v) ≤ 10 ∧
    (∑ v ∈ valuationMasks 2, twistLowPopcountWeight v) ≤ 4 := by
  simp only [valuationMasks, maskSet_eq_fastCertificate]
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
