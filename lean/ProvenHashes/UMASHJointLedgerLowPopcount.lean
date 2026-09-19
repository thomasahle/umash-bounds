import ProvenHashes.UMASHJointLedgerLowCertificate
import ProvenHashes.UMASHTwistPopcount
import ProvenHashes.UMASHPHENHProbability

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet lowTargetK phenhENHMask

/-- Bound an entire low ledger using one target ceiling and the total low
twisting weight. This works for every shuffler, not just the fifteen used by UMASH. -/
theorem phenh_low_ledger_uniform_bound (r s : ℕ) (C W : ℚ≥0)
    (hC : ∀ e, lowTargetK r e ≤ C)
    (hW : (∑ v ∈ valuationMasks r, twistLowWeight v) ≤ W) :
    phenhLowLedger r s ≤ 2^r*(valuationMasks r).card*C*W := by
  have hsum (T : Finset ℕ) (g : ℕ → ℕ → ℚ≥0) (w : ℕ → ℚ≥0)
      (hg : ∀ u v, g u v ≤ C) (hw : (∑ v ∈ T, w v) ≤ W) :
      (∑ u ∈ T, ∑ v ∈ T, g u v*w v) ≤ T.card*C*W := by
    calc
      _ ≤ ∑ _u ∈ T, C*W := by
        apply Finset.sum_le_sum
        intro u _
        calc
          _ ≤ ∑ v ∈ T, C*w v := by
            apply Finset.sum_le_sum
            intro v _
            exact mul_le_mul_of_nonneg_right (hg u v) (by positivity)
          _ = C * ∑ v ∈ T, w v := (Finset.mul_sum ..).symm
          _ ≤ C*W := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hb := hsum (valuationMasks r) (fun u v => lowTargetK r (phenhENHMask s u v))
    twistLowWeight (fun _ _ => hC _) hW
  have hm := mul_le_mul_of_nonneg_left hb (show (0:ℚ≥0) ≤ 2^r by positivity)
  simpa only [phenhLowLedger, mul_assoc] using hm
-- CHECKPOINT

end ProvenHashes.UMASH
