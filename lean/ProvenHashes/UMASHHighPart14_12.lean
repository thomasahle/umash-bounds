import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart14_12_certificate :
    ledgerPackedSum highLedgerPart14_12 highLedgerPrepared14 = 14961798178858590801704609184 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
