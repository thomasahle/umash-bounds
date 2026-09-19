import ProvenHashes.UMASHJointLedger

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The r=3 row uses exactly two admissible low masks. -/
theorem valuationMasks_three_exact : valuationMasks 3 = {0, 18446744073709551608} := by
  unfold valuationMasks
  rw [maskSet_eq_certificate]
  decide +kernel
-- CHECKPOINT

/-- All fifteen r=3 shufflers satisfy the displayed PROOF2 row maximum.
This is an exact rational computation checked by the Lean kernel. -/
theorem phenh_low_ledger_r3_certificate :
    ∀ s : Fin 15, phenhLowLedger 3 (s.val+1) ≤ 268435521 := by
  simp only [phenhLowLedger, valuationMasks_three_exact]
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
