import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart11_15_certificate :
    ledgerPackedSum highLedgerPart11_15 highLedgerPrepared11 = 18509325123450923974424461960 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
