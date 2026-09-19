import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart2_1_certificate :
    ledgerPackedSum highLedgerPart2_1 highLedgerPrepared2 = 83789743655361648591717822432 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
