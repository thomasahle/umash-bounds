import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart12_21_certificate :
    ledgerPackedSum highLedgerPart12_21 highLedgerPrepared12 = 14730679406849240663889450048 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
