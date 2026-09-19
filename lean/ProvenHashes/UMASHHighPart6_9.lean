import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart6_9_certificate :
    ledgerPackedSum highLedgerPart6_9 highLedgerPrepared6 = 11253535678905297729965429528 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
