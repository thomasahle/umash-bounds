import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart6_5_certificate :
    ledgerPackedSum highLedgerPart6_5 highLedgerPrepared6 = 10066761096858454018000386912 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
