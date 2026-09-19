import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart15_14_certificate :
    ledgerPackedSum highLedgerPart15_14 highLedgerPrepared15 = 17799293457722987510534132832 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
