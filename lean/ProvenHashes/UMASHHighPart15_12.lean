import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart15_12_certificate :
    ledgerPackedSum highLedgerPart15_12 highLedgerPrepared15 = 16266520086892242360737154272 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
