import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart1_18_certificate :
    ledgerPackedSum highLedgerPart1_18 highLedgerPrepared1 = 20810441359385321876097809888 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
