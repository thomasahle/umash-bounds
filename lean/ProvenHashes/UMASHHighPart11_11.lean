import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart11_11_certificate :
    ledgerPackedSum highLedgerPart11_11 highLedgerPrepared11 = 14420234958952429302731955200 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
