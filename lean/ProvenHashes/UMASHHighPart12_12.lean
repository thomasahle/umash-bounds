import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart12_12_certificate :
    ledgerPackedSum highLedgerPart12_12 highLedgerPrepared12 = 16786289424456432240445271456 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
