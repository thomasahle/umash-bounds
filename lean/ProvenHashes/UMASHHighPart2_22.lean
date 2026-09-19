import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart2_22_certificate :
    ledgerPackedSum highLedgerPart2_22 highLedgerPrepared2 = 114883028349442131733572936576 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
