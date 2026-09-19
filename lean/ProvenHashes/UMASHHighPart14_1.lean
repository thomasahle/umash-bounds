import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart14_1_certificate :
    ledgerPackedSum highLedgerPart14_1 highLedgerPrepared14 = 13844892537693327179600779872 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
