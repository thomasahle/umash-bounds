import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart1_3_certificate :
    ledgerPackedSum highLedgerPart1_3 highLedgerPrepared1 = 56092844352762443037824389936 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
