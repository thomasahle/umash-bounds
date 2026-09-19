import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart2_6_certificate :
    ledgerPackedSum highLedgerPart2_6 highLedgerPrepared2 = 89825551681831095452707592288 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
