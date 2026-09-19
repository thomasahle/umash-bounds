import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart9_7_certificate :
    ledgerPackedSum highLedgerPart9_7 highLedgerPrepared9 = 6318423774861644614073382384 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
