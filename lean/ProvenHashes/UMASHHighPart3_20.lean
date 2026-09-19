import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart3_20_certificate :
    ledgerPackedSum highLedgerPart3_20 highLedgerPrepared3 = 27461705456474721218963397504 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
