import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart7_13_certificate :
    ledgerPackedSum highLedgerPart7_13 highLedgerPrepared7 = 19168770477395245738340070976 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
