import ProvenHashes.UMASHLowWeightCertificate

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] maskSet

/-- Exact low twisting weights improve the popcount-only ceiling 10 to 6.
Only the 248 even projection masks are enumerated, never the key space. -/
theorem twist_low_weight_sum_six :
    (∑ v ∈ valuationMasks 1, twistLowWeight v) ≤ 6 := by
  simp only [valuationMasks, maskSet_eq_fastCertificate]
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
