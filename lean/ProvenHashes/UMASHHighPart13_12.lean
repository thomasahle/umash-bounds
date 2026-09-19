import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart13_12_certificate :
    ledgerPackedSum highLedgerPart13_12 highLedgerPrepared13 = 13062020801093694637337343776 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
