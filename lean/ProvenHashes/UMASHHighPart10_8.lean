import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart10_8_certificate :
    ledgerPackedSum highLedgerPart10_8 highLedgerPrepared10 = 16469898686934186901770410112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
