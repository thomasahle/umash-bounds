import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart2_0_certificate :
    ledgerPackedSum highLedgerPart2_0 highLedgerPrepared2 = 84992011723166582436408054336 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
