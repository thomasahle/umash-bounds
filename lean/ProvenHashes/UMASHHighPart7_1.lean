import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart7_1_certificate :
    ledgerPackedSum highLedgerPart7_1 highLedgerPrepared7 = 13023665598910129598882140656 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
