import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart9_26_certificate :
    ledgerPackedSum highLedgerPart9_26 highLedgerPrepared9 = 3863638630360406527668792592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
