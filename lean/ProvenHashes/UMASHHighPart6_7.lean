import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart6_7_certificate :
    ledgerPackedSum highLedgerPart6_7 highLedgerPrepared6 = 7798229300653805947325412432 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
