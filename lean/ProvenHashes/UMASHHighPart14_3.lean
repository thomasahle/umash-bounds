import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart14_3_certificate :
    ledgerPackedSum highLedgerPart14_3 highLedgerPrepared14 = 16265814582090898002957980488 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
