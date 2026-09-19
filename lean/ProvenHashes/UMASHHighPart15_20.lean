import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart15_20_certificate :
    ledgerPackedSum highLedgerPart15_20 highLedgerPrepared15 = 17258301112885153885148425744 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
