import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart5_15_certificate :
    ledgerPackedSum highLedgerPart5_15 highLedgerPrepared5 = 26493370960153360648873788104 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
