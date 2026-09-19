import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart2_3_certificate :
    ledgerPackedSum highLedgerPart2_3 highLedgerPrepared2 = 112739974156813649355310204296 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
