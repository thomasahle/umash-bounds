import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart4_9_certificate :
    ledgerPackedSum highLedgerPart4_9 highLedgerPrepared4 = 16065925986024901428304318024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
