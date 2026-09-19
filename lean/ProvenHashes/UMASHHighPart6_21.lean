import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart6_21_certificate :
    ledgerPackedSum highLedgerPart6_21 highLedgerPrepared6 = 13298138566572914231575600832 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
