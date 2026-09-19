import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart1_16_certificate :
    ledgerPackedSum highLedgerPart1_16 highLedgerPrepared1 = 10284754995954002502380521728 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
