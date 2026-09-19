import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart3_11_certificate :
    ledgerPackedSum highLedgerPart3_11 highLedgerPrepared3 = 28318187055258856642098054592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
