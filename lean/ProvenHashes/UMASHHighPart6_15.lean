import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart6_15_certificate :
    ledgerPackedSum highLedgerPart6_15 highLedgerPrepared6 = 10082455077556025350838831080 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
