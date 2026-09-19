import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart6_17_certificate :
    ledgerPackedSum highLedgerPart6_17 highLedgerPrepared6 = 15352322839287345977265631520 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
