import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart10_3_certificate :
    ledgerPackedSum highLedgerPart10_3 highLedgerPrepared10 = 16452634691223518613054853672 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
