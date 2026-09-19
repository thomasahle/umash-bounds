import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart1_7_certificate :
    ledgerPackedSum highLedgerPart1_7 highLedgerPrepared1 = 6248890623697734665018784800 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
