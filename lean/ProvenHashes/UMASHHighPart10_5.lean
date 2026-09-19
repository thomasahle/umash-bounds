import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart10_5_certificate :
    ledgerPackedSum highLedgerPart10_5 highLedgerPrepared10 = 13481293811578973820839153792 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
