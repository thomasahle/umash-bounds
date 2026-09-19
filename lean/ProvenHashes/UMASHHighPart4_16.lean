import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart4_16_certificate :
    ledgerPackedSum highLedgerPart4_16 highLedgerPrepared4 = 16131306513502798317041991104 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
