import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart3_5_certificate :
    ledgerPackedSum highLedgerPart3_5 highLedgerPrepared3 = 19631648010643681642239560064 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
