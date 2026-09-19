import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart9_14_certificate :
    ledgerPackedSum highLedgerPart9_14 highLedgerPrepared9 = 7537906638113777325932449120 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
