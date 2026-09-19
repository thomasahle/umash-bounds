import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart6_11_certificate :
    ledgerPackedSum highLedgerPart6_11 highLedgerPrepared6 = 14271528633440386316614533632 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
