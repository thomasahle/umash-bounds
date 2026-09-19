import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart15_10_certificate :
    ledgerPackedSum highLedgerPart15_10 highLedgerPrepared15 = 21994491446684650630158526656 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
