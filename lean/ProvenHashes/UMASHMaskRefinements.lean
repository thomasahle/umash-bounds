import ProvenHashes.UMASHPatternCertificate

namespace ProvenHashes.UMASH
set_option maxRecDepth 32768
set_option maxHeartbeats 0
attribute [local irreducible] maskSet


theorem valuationMasks_card_table :
    (valuationMasks 0).card = 852 ∧ (valuationMasks 1).card = 248 ∧
    (valuationMasks 2).card = 64 ∧ (valuationMasks 3).card = 2 ∧
    (valuationMasks 4).card = 1 := by
  unfold valuationMasks
  rw [maskSet_eq_certificate]
  decide +kernel


theorem maskSet_low_high_counts :
    (maskSet.filter (fun d => d % 2 = 0)).card = 248 ∧
    (maskSet.filter (fun d => d % 2 = 1)).card = 604 ∧
    (maskSet.filter (fun d => d / 2^63 = 0)).card = 248 ∧
    (maskSet.filter (fun d => d / 2^63 = 1)).card = 604 := by
  rw [maskSet_eq_certificate]
  decide +kernel


theorem maskSet_mod_sixteen : maskSet.filter (fun d => d % 16 = 0) = {0} := by
  rw [maskSet_eq_certificate]
  decide +kernel


theorem maskSet_nonzero_large : ∀ d ∈ maskSet, d ≠ 0 → 2^60 ≤ d := by
  rw [maskSet_eq_certificate]
  decide +kernel

end ProvenHashes.UMASH
