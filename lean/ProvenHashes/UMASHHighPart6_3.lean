import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart6_3_certificate :
    ledgerPackedSum highLedgerPart6_3 highLedgerPrepared6 = 9169922570701624728151515944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
