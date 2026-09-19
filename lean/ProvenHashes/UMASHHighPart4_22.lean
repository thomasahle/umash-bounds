import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart4_22_certificate :
    ledgerPackedSum highLedgerPart4_22 highLedgerPrepared4 = 14285437927079440694843247136 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
