import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart4_18_certificate :
    ledgerPackedSum highLedgerPart4_18 highLedgerPrepared4 = 16418250168600592880812336368 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
