import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart5_8_certificate :
    ledgerPackedSum highLedgerPart5_8 highLedgerPrepared5 = 21051987131465160754980648000 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
