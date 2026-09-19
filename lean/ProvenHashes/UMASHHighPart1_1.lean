import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart1_1_certificate :
    ledgerPackedSum highLedgerPart1_1 highLedgerPrepared1 = 71559662793826961779836154152 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
