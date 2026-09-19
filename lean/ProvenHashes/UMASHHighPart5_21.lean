import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart5_21_certificate :
    ledgerPackedSum highLedgerPart5_21 highLedgerPrepared5 = 17777982188964366801444929216 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
