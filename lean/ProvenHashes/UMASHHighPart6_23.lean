import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart6_23_certificate :
    ledgerPackedSum highLedgerPart6_23 highLedgerPrepared6 = 16633097036498942112687081952 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
