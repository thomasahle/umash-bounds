import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart14_14_certificate :
    ledgerPackedSum highLedgerPart14_14 highLedgerPrepared14 = 19215236441021896072398171552 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
