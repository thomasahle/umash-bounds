import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart12_15_certificate :
    ledgerPackedSum highLedgerPart12_15 highLedgerPrepared12 = 17712277198864935369350421864 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
