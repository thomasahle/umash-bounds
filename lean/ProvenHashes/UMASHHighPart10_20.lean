import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart10_20_certificate :
    ledgerPackedSum highLedgerPart10_20 highLedgerPrepared10 = 19667589095995839000246952304 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
