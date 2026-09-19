import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart11_8_certificate :
    ledgerPackedSum highLedgerPart11_8 highLedgerPrepared11 = 15869193183711490899392468608 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
