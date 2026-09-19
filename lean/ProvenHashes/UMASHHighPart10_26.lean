import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart10_26_certificate :
    ledgerPackedSum highLedgerPart10_26 highLedgerPrepared10 = 18796454167862907679572690448 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
