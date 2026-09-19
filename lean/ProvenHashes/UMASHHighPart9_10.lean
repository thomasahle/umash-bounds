import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart9_10_certificate :
    ledgerPackedSum highLedgerPart9_10 highLedgerPrepared9 = 10259461202103733242807735360 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
