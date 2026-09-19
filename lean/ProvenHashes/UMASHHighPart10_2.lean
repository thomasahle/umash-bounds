import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart10_2_certificate :
    ledgerPackedSum highLedgerPart10_2 highLedgerPrepared10 = 15296925541188066698993198976 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
