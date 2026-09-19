import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart7_15_certificate :
    ledgerPackedSum highLedgerPart7_15 highLedgerPrepared7 = 16150878898054767813276312040 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
