import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart12_23_certificate :
    ledgerPackedSum highLedgerPart12_23 highLedgerPrepared12 = 18227031863397671192884514848 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
