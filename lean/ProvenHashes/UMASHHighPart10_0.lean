import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart10_0_certificate :
    ledgerPackedSum highLedgerPart10_0 highLedgerPrepared10 = 15967844115453045300789755712 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
