import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart5_12_certificate :
    ledgerPackedSum highLedgerPart5_12 highLedgerPrepared5 = 19010110882614308014955308864 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
