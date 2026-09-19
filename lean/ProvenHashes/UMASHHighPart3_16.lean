import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart3_16_certificate :
    ledgerPackedSum highLedgerPart3_16 highLedgerPrepared3 = 28015515460732626133333837056 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
