import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart2_15_certificate :
    ledgerPackedSum highLedgerPart2_15 highLedgerPrepared2 = 150590648895269776044087862424 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
