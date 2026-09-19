import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart5_23_certificate :
    ledgerPackedSum highLedgerPart5_23 highLedgerPrepared5 = 16793923029796962387748930688 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
