import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart12_9_certificate :
    ledgerPackedSum highLedgerPart12_9 highLedgerPrepared12 = 18631248549279734138675496024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
