import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart3_9_certificate :
    ledgerPackedSum highLedgerPart3_9 highLedgerPrepared3 = 29859204386116204244206591520 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
