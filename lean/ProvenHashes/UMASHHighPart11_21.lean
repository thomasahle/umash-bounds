import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart11_21_certificate :
    ledgerPackedSum highLedgerPart11_21 highLedgerPrepared11 = 14145148632137595210616396416 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
