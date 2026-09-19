import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart12_20_certificate :
    ledgerPackedSum highLedgerPart12_20 highLedgerPrepared12 = 14739703324662738465913761024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
