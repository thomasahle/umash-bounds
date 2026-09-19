import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart15_16_certificate :
    ledgerPackedSum highLedgerPart15_16 highLedgerPrepared15 = 16474917886560119212151391616 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
