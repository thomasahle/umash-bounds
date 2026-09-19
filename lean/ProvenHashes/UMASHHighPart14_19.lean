import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart14_19_certificate :
    ledgerPackedSum highLedgerPart14_19 highLedgerPrepared14 = 34410081508292290841750395072 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
