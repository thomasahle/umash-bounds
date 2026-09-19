import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart5_18_certificate :
    ledgerPackedSum highLedgerPart5_18 highLedgerPrepared5 = 30163635214787492812371854896 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
