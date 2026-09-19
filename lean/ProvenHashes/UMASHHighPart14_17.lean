import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart14_17_certificate :
    ledgerPackedSum highLedgerPart14_17 highLedgerPrepared14 = 17624369163512031941215594112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
