import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart12_6_certificate :
    ledgerPackedSum highLedgerPart12_6 highLedgerPrepared12 = 10679313435638162411075151328 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
