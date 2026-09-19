import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart2_23_certificate :
    ledgerPackedSum highLedgerPart2_23 highLedgerPrepared2 = 113074440458177778308326963712 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
