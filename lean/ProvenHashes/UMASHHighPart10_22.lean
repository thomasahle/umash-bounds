import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart10_22_certificate :
    ledgerPackedSum highLedgerPart10_22 highLedgerPrepared10 = 17323968989930727989649628832 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
