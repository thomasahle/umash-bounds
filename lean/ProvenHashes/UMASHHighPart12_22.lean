import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart12_22_certificate :
    ledgerPackedSum highLedgerPart12_22 highLedgerPrepared12 = 15849581285533514690274234080 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
