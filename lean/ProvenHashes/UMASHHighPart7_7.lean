import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart7_7_certificate :
    ledgerPackedSum highLedgerPart7_7 highLedgerPrepared7 = 13115441108088135127988302864 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
