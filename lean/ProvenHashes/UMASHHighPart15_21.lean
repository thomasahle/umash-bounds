import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart15_21_certificate :
    ledgerPackedSum highLedgerPart15_21 highLedgerPrepared15 = 15670137294092236954457275936 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
