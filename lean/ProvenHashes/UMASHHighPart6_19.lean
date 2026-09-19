import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart6_19_certificate :
    ledgerPackedSum highLedgerPart6_19 highLedgerPrepared6 = 10706959701595766263537489504 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
