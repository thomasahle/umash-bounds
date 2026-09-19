import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart2_17_certificate :
    ledgerPackedSum highLedgerPart2_17 highLedgerPrepared2 = 120027836644593115337467692992 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
