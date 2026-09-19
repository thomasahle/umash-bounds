import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart9_21_certificate :
    ledgerPackedSum highLedgerPart9_21 highLedgerPrepared9 = 12609278822914984637411077184 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
