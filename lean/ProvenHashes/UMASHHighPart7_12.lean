import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart7_12_certificate :
    ledgerPackedSum highLedgerPart7_12 highLedgerPrepared7 = 15053421958915970255604651584 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
