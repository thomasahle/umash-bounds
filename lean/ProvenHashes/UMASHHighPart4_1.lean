import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart4_1_certificate :
    ledgerPackedSum highLedgerPart4_1 highLedgerPrepared4 = 10733728931271576451067547488 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
