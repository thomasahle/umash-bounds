import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart6_10_certificate :
    ledgerPackedSum highLedgerPart6_10 highLedgerPrepared6 = 11444277137676329417201971664 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
