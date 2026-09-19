import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart5_9_certificate :
    ledgerPackedSum highLedgerPart5_9 highLedgerPrepared5 = 27594700782326086332969296592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
