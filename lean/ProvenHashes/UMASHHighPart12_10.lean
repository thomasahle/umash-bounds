import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart12_10_certificate :
    ledgerPackedSum highLedgerPart12_10 highLedgerPrepared12 = 17176154772450868028736433024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
