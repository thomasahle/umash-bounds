import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart3_22_certificate :
    ledgerPackedSum highLedgerPart3_22 highLedgerPrepared3 = 26853052467893556177773472800 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
