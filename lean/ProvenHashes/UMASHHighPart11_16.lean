import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart11_16_certificate :
    ledgerPackedSum highLedgerPart11_16 highLedgerPrepared11 = 15465233810201024956914953600 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
