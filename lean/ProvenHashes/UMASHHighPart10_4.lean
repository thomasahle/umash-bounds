import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart10_4_certificate :
    ledgerPackedSum highLedgerPart10_4 highLedgerPrepared10 = 14638956866204193802847211056 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
