import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart10_23_certificate :
    ledgerPackedSum highLedgerPart10_23 highLedgerPrepared10 = 17028843768456212376126065376 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
