import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart1_15_certificate :
    ledgerPackedSum highLedgerPart1_15 highLedgerPrepared1 = 2514038967062566690827088360 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
