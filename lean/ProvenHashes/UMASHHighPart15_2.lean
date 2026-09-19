import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart15_2_certificate :
    ledgerPackedSum highLedgerPart15_2 highLedgerPrepared15 = 16657382706779363627492357632 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
