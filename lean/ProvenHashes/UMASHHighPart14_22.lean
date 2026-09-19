import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart14_22_certificate :
    ledgerPackedSum highLedgerPart14_22 highLedgerPrepared14 = 15012833247672531865452145152 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
