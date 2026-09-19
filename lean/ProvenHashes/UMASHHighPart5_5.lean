import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart5_5_certificate :
    ledgerPackedSum highLedgerPart5_5 highLedgerPrepared5 = 12485411206649025532991202848 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
