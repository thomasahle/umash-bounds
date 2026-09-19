import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart15_26_certificate :
    ledgerPackedSum highLedgerPart15_26 highLedgerPrepared15 = 10365654673229446838516597968 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
