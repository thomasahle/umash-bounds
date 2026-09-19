import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart10_11_certificate :
    ledgerPackedSum highLedgerPart10_11 highLedgerPrepared10 = 17048410033699732661862940192 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
