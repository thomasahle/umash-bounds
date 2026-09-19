import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart2_10_certificate :
    ledgerPackedSum highLedgerPart2_10 highLedgerPrepared2 = 125949823571766706765621706640 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
