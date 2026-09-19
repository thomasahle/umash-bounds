import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart13_18_certificate :
    ledgerPackedSum highLedgerPart13_18 highLedgerPrepared13 = 16578472365750869322239148048 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
