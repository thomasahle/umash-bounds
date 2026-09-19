import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart14_5_certificate :
    ledgerPackedSum highLedgerPart14_5 highLedgerPrepared14 = 10231273905881208711089535744 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
