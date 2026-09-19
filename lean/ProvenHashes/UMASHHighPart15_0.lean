import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart15_0_certificate :
    ledgerPackedSum highLedgerPart15_0 highLedgerPrepared15 = 20903216829270983240707465952 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
