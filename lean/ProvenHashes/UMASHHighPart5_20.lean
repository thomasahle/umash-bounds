import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart5_20_certificate :
    ledgerPackedSum highLedgerPart5_20 highLedgerPrepared5 = 22111296770270378966524133344 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
