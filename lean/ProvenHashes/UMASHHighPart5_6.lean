import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart5_6_certificate :
    ledgerPackedSum highLedgerPart5_6 highLedgerPrepared5 = 13763176956136019647675635840 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
