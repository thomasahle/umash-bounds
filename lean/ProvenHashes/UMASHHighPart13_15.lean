import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart13_15_certificate :
    ledgerPackedSum highLedgerPart13_15 highLedgerPrepared13 = 19007546327169686999170027368 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
