import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart3_18_certificate :
    ledgerPackedSum highLedgerPart3_18 highLedgerPrepared3 = 29397526570574971643311687064 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
