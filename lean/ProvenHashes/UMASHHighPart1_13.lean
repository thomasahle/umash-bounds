import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart1_13_certificate :
    ledgerPackedSum highLedgerPart1_13 highLedgerPrepared1 = 91889646061620849585919603064 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
