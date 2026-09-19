import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart9_0_certificate :
    ledgerPackedSum highLedgerPart9_0 highLedgerPrepared9 = 8361135313215663881890436224 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
