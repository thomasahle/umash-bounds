import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart10_17_certificate :
    ledgerPackedSum highLedgerPart10_17 highLedgerPrepared10 = 17887316688681940360670969344 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
