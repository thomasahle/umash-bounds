import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart2_12_certificate :
    ledgerPackedSum highLedgerPart2_12 highLedgerPrepared2 = 114829796285065816405800258944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
