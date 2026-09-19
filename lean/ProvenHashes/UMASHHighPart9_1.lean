import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart9_1_certificate :
    ledgerPackedSum highLedgerPart9_1 highLedgerPrepared9 = 5938773487136506345530982128 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
