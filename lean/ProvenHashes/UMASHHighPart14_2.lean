import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart14_2_certificate :
    ledgerPackedSum highLedgerPart14_2 highLedgerPrepared14 = 15218332557139398417016812544 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
