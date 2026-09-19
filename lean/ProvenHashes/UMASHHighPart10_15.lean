import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart10_15_certificate :
    ledgerPackedSum highLedgerPart10_15 highLedgerPrepared10 = 24873159866110028583826819560 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
