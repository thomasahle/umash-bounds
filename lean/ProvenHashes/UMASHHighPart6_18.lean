import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart6_18_certificate :
    ledgerPackedSum highLedgerPart6_18 highLedgerPrepared6 = 11360545765809094443459152000 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
