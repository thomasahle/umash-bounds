import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart1_0_certificate :
    ledgerPackedSum highLedgerPart1_0 highLedgerPrepared1 = 15052292013999339354491077952 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
