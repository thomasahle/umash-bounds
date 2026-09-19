import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart1_17_certificate :
    ledgerPackedSum highLedgerPart1_17 highLedgerPrepared1 = 146329025506582980126555208832 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
