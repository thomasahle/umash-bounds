import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart13_7_certificate :
    ledgerPackedSum highLedgerPart13_7 highLedgerPrepared13 = 14218128377681729017014888688 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
