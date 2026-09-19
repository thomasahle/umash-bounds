import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart9_15_certificate :
    ledgerPackedSum highLedgerPart9_15 highLedgerPrepared9 = 10188357064843652785237046056 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
