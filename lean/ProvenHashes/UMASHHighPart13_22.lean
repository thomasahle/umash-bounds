import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart13_22_certificate :
    ledgerPackedSum highLedgerPart13_22 highLedgerPrepared13 = 14159273560489317460346652320 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
