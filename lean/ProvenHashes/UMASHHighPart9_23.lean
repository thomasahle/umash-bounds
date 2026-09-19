import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart9_23_certificate :
    ledgerPackedSum highLedgerPart9_23 highLedgerPrepared9 = 10686466096587406609155830944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
