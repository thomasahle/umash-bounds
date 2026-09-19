import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart11_10_certificate :
    ledgerPackedSum highLedgerPart11_10 highLedgerPrepared11 = 16117675072919756187357513504 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
