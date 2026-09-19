import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart1_5_certificate :
    ledgerPackedSum highLedgerPart1_5 highLedgerPrepared1 = 88045720144376164421746819744 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
