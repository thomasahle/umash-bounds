import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart5_14_certificate :
    ledgerPackedSum highLedgerPart5_14 highLedgerPrepared5 = 28092428235914273676664040208 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
