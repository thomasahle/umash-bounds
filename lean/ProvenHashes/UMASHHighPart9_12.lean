import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart9_12_certificate :
    ledgerPackedSum highLedgerPart9_12 highLedgerPrepared9 = 10302034354275920671544880128 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
