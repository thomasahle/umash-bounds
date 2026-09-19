import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart4_17_certificate :
    ledgerPackedSum highLedgerPart4_17 highLedgerPrepared4 = 15883039432253562867054183552 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
