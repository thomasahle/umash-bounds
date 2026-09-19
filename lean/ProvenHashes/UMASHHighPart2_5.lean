import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart2_5_certificate :
    ledgerPackedSum highLedgerPart2_5 highLedgerPrepared2 = 87998896636528721057688214944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
