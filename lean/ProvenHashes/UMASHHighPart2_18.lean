import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart2_18_certificate :
    ledgerPackedSum highLedgerPart2_18 highLedgerPrepared2 = 142210199110416032152608798736 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
