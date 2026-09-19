import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart1_10_certificate :
    ledgerPackedSum highLedgerPart1_10 highLedgerPrepared1 = 197720965013503328581797688 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
