import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart10_10_certificate :
    ledgerPackedSum highLedgerPart10_10 highLedgerPrepared10 = 18521638651499118467608842496 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
