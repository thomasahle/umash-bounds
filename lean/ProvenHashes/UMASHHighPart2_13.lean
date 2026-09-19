import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart2_13_certificate :
    ledgerPackedSum highLedgerPart2_13 highLedgerPrepared2 = 118920438737375889857491699040 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
