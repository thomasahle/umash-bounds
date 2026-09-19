import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart5_26_certificate :
    ledgerPackedSum highLedgerPart5_26 highLedgerPrepared5 = 18063156794304446549625660400 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
