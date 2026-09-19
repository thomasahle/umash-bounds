import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart15_22_certificate :
    ledgerPackedSum highLedgerPart15_22 highLedgerPrepared15 = 16857523652390704080692462656 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
