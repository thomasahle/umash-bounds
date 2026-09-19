import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart15_1_certificate :
    ledgerPackedSum highLedgerPart15_1 highLedgerPrepared15 = 12726085723549480581827290224 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
