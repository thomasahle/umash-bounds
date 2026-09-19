import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart12_0_certificate :
    ledgerPackedSum highLedgerPart12_0 highLedgerPrepared12 = 13041485084366983493060471264 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
