import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart6_0_certificate :
    ledgerPackedSum highLedgerPart6_0 highLedgerPrepared6 = 9261010145896653990439841088 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
