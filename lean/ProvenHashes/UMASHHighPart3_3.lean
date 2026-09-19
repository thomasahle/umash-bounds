import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart3_3_certificate :
    ledgerPackedSum highLedgerPart3_3 highLedgerPrepared3 = 21223338629257985457189525304 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
