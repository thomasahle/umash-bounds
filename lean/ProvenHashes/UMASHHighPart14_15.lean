import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart14_15_certificate :
    ledgerPackedSum highLedgerPart14_15 highLedgerPrepared14 = 25587264578716012860648411944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
