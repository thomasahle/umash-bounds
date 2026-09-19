import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart3_12_certificate :
    ledgerPackedSum highLedgerPart3_12 highLedgerPrepared3 = 28721822443557006956751127392 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
