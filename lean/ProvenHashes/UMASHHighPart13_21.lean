import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart13_21_certificate :
    ledgerPackedSum highLedgerPart13_21 highLedgerPrepared13 = 14924463935772048751688028064 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
