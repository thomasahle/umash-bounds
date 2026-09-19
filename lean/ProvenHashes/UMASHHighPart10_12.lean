import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart10_12_certificate :
    ledgerPackedSum highLedgerPart10_12 highLedgerPrepared10 = 18190700582684469426777627584 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
