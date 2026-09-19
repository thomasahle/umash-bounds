import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart6_12_certificate :
    ledgerPackedSum highLedgerPart6_12 highLedgerPrepared6 = 14761876568581662217147864128 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
