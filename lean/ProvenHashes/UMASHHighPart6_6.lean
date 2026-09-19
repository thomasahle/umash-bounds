import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart6_6_certificate :
    ledgerPackedSum highLedgerPart6_6 highLedgerPrepared6 = 11991729455426900091873356736 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
