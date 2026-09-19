import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart4_15_certificate :
    ledgerPackedSum highLedgerPart4_15 highLedgerPrepared4 = 16494051220253821208261003784 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
