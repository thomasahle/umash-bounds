import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart3_17_certificate :
    ledgerPackedSum highLedgerPart3_17 highLedgerPrepared3 = 27640349056966268690529372736 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
