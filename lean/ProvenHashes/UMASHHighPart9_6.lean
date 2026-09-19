import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart9_6_certificate :
    ledgerPackedSum highLedgerPart9_6 highLedgerPrepared9 = 6483726294218720057956894144 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
