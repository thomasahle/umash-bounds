import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart6_22_certificate :
    ledgerPackedSum highLedgerPart6_22 highLedgerPrepared6 = 14315585637035979216940888928 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
