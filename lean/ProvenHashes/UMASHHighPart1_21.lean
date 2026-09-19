import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart1_21_certificate :
    ledgerPackedSum highLedgerPart1_21 highLedgerPrepared1 = 4683764981571532649095754592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
