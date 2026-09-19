import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart8_1_certificate :
    ledgerPackedSum highLedgerPart8_1 highLedgerPrepared8 = 6218095027544399783505591360 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
