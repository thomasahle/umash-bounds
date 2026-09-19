import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart7_9_certificate :
    ledgerPackedSum highLedgerPart7_9 highLedgerPrepared7 = 17321747340269836408327807600 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
