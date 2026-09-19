import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart5_16_certificate :
    ledgerPackedSum highLedgerPart5_16 highLedgerPrepared5 = 20761900836442511346811293728 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
