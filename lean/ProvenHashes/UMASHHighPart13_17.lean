import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart13_17_certificate :
    ledgerPackedSum highLedgerPart13_17 highLedgerPrepared13 = 17674990638517325594328665856 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
