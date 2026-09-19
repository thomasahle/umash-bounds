import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart13_1_certificate :
    ledgerPackedSum highLedgerPart13_1 highLedgerPrepared13 = 9160242770759623719608201648 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
