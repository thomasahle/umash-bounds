import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart3_26_certificate :
    ledgerPackedSum highLedgerPart3_26 highLedgerPrepared3 = 19560144179409015587053724112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
