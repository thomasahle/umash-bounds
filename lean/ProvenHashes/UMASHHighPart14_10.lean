import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart14_10_certificate :
    ledgerPackedSum highLedgerPart14_10 highLedgerPrepared14 = 20736868532098565531411228384 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
