import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart15_15_certificate :
    ledgerPackedSum highLedgerPart15_15 highLedgerPrepared15 = 28188031177331524422410670856 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
