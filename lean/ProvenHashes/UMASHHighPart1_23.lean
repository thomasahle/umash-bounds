import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart1_23_certificate :
    ledgerPackedSum highLedgerPart1_23 highLedgerPrepared1 = 191044586369502763424057923424 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
