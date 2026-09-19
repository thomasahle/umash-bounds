import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart1_12_certificate :
    ledgerPackedSum highLedgerPart1_12 highLedgerPrepared1 = 147856255027770193541958317568 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
