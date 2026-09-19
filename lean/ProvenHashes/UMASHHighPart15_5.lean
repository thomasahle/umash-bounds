import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart15_5_certificate :
    ledgerPackedSum highLedgerPart15_5 highLedgerPrepared15 = 11766749423413155269861357888 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
