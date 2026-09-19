import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart4_20_certificate :
    ledgerPackedSum highLedgerPart4_20 highLedgerPrepared4 = 14665611840416722210518797536 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
