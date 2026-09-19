import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart3_21_certificate :
    ledgerPackedSum highLedgerPart3_21 highLedgerPrepared3 = 26988851499173433387178863872 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
