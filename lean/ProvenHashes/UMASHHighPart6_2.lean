import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart6_2_certificate :
    ledgerPackedSum highLedgerPart6_2 highLedgerPrepared6 = 9713092781682860757975879840 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
