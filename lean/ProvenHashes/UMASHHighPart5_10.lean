import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart5_10_certificate :
    ledgerPackedSum highLedgerPart5_10 highLedgerPrepared5 = 27688292179519204023734570400 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
