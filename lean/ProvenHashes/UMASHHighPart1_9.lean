import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart1_9_certificate :
    ledgerPackedSum highLedgerPart1_9 highLedgerPrepared1 = 16762025971643232541128355784 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
