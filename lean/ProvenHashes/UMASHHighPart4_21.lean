import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart4_21_certificate :
    ledgerPackedSum highLedgerPart4_21 highLedgerPrepared4 = 16126851165255950318096892224 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
