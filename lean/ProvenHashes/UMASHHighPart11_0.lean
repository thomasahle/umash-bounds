import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart11_0_certificate :
    ledgerPackedSum highLedgerPart11_0 highLedgerPrepared11 = 13396317694378852794810343456 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
