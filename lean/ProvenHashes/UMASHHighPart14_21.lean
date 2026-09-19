import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart14_21_certificate :
    ledgerPackedSum highLedgerPart14_21 highLedgerPrepared14 = 14750467330893672099154985344 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
