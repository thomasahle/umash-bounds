import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart5_1_certificate :
    ledgerPackedSum highLedgerPart5_1 highLedgerPrepared5 = 16670441031105700824979584368 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
