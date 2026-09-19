import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart2_21_certificate :
    ledgerPackedSum highLedgerPart2_21 highLedgerPrepared2 = 115211408511556154661096412064 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
