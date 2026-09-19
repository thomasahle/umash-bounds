import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart5_22_certificate :
    ledgerPackedSum highLedgerPart5_22 highLedgerPrepared5 = 18424841648904668835734210208 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
