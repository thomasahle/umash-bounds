import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart14_9_certificate :
    ledgerPackedSum highLedgerPart14_9 highLedgerPrepared14 = 28240837143470177879237644680 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
