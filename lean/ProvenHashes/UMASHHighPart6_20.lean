import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart6_20_certificate :
    ledgerPackedSum highLedgerPart6_20 highLedgerPrepared6 = 11974042317801888689101434016 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
