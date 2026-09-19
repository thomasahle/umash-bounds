import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart2_2_certificate :
    ledgerPackedSum highLedgerPart2_2 highLedgerPrepared2 = 108766994680311329316370551008 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
