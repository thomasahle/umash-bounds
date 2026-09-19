import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart9_13_certificate :
    ledgerPackedSum highLedgerPart9_13 highLedgerPrepared9 = 9718638450256798195891346080 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
