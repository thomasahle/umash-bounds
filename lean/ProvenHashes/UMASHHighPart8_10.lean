import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart8_10_certificate :
    ledgerPackedSum highLedgerPart8_10 highLedgerPrepared8 = 11611680445511048571349046208 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
