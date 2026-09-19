import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart7_26_certificate :
    ledgerPackedSum highLedgerPart7_26 highLedgerPrepared7 = 8906652492349193546978137840 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
