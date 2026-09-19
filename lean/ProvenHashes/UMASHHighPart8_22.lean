import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart8_22_certificate :
    ledgerPackedSum highLedgerPart8_22 highLedgerPrepared8 = 15164228481553113012569987136 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
