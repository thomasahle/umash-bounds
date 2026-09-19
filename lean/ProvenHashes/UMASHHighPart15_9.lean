import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart15_9_certificate :
    ledgerPackedSum highLedgerPart15_9 highLedgerPrepared15 = 30635043678355196134523621088 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
