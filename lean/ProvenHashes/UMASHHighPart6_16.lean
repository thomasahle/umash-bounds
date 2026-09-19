import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart6_16_certificate :
    ledgerPackedSum highLedgerPart6_16 highLedgerPrepared6 = 14397179468699093592245002592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
