import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart2_9_certificate :
    ledgerPackedSum highLedgerPart2_9 highLedgerPrepared2 = 143728376957332948399931864816 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
