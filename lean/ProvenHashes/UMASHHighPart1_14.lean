import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart1_14_certificate :
    ledgerPackedSum highLedgerPart1_14 highLedgerPrepared1 = 16132508260059492456115687016 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
