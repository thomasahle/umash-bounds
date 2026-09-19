import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart3_8_certificate :
    ledgerPackedSum highLedgerPart3_8 highLedgerPrepared3 = 27874977680635535606515950592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
