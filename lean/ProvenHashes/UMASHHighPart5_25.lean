import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart5_25_certificate :
    ledgerPackedSum highLedgerPart5_25 highLedgerPrepared5 = 27488681760543457264619407672 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
