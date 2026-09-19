import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart5_13_certificate :
    ledgerPackedSum highLedgerPart5_13 highLedgerPrepared5 = 19170926813258162677253589312 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
