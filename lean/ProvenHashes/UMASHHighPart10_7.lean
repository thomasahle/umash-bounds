import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart10_7_certificate :
    ledgerPackedSum highLedgerPart10_7 highLedgerPrepared10 = 19964520702603811827512096272 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
