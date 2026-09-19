import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart15_17_certificate :
    ledgerPackedSum highLedgerPart15_17 highLedgerPrepared15 = 15932999728709584928265259008 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
