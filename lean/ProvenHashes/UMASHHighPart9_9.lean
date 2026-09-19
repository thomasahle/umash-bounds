import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart9_9_certificate :
    ledgerPackedSum highLedgerPart9_9 highLedgerPrepared9 = 9626521116072765497743930320 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
