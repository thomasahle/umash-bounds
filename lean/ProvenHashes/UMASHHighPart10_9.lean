import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart10_9_certificate :
    ledgerPackedSum highLedgerPart10_9 highLedgerPrepared10 = 23827532909803853928921924360 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
