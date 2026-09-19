import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart6_4_certificate :
    ledgerPackedSum highLedgerPart6_4 highLedgerPrepared6 = 8450522789828120363939873808 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
