import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart5_7_certificate :
    ledgerPackedSum highLedgerPart5_7 highLedgerPrepared5 = 21175834772340372923003098576 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
