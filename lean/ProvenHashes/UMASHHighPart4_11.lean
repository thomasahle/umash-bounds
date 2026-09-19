import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart4_11_certificate :
    ledgerPackedSum highLedgerPart4_11 highLedgerPrepared4 = 16117285724326516109714102784 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
