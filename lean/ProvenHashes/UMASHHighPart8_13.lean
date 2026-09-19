import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart8_13_certificate :
    ledgerPackedSum highLedgerPart8_13 highLedgerPrepared8 = 11044016268939561046831986656 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
