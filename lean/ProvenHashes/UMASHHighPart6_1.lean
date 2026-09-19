import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart6_1_certificate :
    ledgerPackedSum highLedgerPart6_1 highLedgerPrepared6 = 9731537575421800777150388064 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
