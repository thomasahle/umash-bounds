import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart6_13_certificate :
    ledgerPackedSum highLedgerPart6_13 highLedgerPrepared6 = 17703777942683101713205127264 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
