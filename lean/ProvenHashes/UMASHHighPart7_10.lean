import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart7_10_certificate :
    ledgerPackedSum highLedgerPart7_10 highLedgerPrepared7 = 14907829178233345230451503056 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
