import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart10_6_certificate :
    ledgerPackedSum highLedgerPart10_6 highLedgerPrepared10 = 12878270028552726710779007264 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
