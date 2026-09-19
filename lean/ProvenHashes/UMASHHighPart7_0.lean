import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart7_0_certificate :
    ledgerPackedSum highLedgerPart7_0 highLedgerPrepared7 = 11834013168704303548777204896 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
