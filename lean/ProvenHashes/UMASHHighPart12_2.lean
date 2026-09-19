import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart12_2_certificate :
    ledgerPackedSum highLedgerPart12_2 highLedgerPrepared12 = 12122879775378703119233939680 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
