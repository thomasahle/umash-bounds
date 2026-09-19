import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart2_7_certificate :
    ledgerPackedSum highLedgerPart2_7 highLedgerPrepared2 = 118026736793995867515598136200 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
