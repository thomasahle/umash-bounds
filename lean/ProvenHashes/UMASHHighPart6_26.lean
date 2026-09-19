import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart6_26_certificate :
    ledgerPackedSum highLedgerPart6_26 highLedgerPrepared6 = 5060210576903274344346889456 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
