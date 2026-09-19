import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart8_12_certificate :
    ledgerPackedSum highLedgerPart8_12 highLedgerPrepared8 = 13458440650381062340889027584 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
