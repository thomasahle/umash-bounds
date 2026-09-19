import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart15_23_certificate :
    ledgerPackedSum highLedgerPart15_23 highLedgerPrepared15 = 14493015994093847679700317248 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
