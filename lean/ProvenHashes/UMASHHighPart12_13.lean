import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart12_13_certificate :
    ledgerPackedSum highLedgerPart12_13 highLedgerPrepared12 = 14440287302995231079148695456 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
