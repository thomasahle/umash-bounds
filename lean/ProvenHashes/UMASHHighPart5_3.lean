import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart5_3_certificate :
    ledgerPackedSum highLedgerPart5_3 highLedgerPrepared5 = 19004779515633024350781231488 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
