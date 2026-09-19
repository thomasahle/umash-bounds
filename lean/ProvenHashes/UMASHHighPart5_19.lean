import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart5_19_certificate :
    ledgerPackedSum highLedgerPart5_19 highLedgerPrepared5 = 28921227345848035983334001024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
