import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart13_23_certificate :
    ledgerPackedSum highLedgerPart13_23 highLedgerPrepared13 = 17806848315438938852115114112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
