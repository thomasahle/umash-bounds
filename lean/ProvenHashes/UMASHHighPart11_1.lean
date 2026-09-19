import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart11_1_certificate :
    ledgerPackedSum highLedgerPart11_1 highLedgerPrepared11 = 12282925304215036425801082160 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
