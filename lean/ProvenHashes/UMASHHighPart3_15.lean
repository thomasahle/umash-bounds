import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart3_15_certificate :
    ledgerPackedSum highLedgerPart3_15 highLedgerPrepared3 = 30254781971124528949743045024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
