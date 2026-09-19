import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart3_23_certificate :
    ledgerPackedSum highLedgerPart3_23 highLedgerPrepared3 = 26920706918260949445049597536 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
