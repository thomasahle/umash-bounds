import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart10_21_certificate :
    ledgerPackedSum highLedgerPart10_21 highLedgerPrepared10 = 17839557252324582441797777056 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
