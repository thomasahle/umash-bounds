import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart5_4_certificate :
    ledgerPackedSum highLedgerPart5_4 highLedgerPrepared5 = 17277110598847116534069993168 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
