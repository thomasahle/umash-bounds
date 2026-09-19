import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart9_11_certificate :
    ledgerPackedSum highLedgerPart9_11 highLedgerPrepared9 = 11599847975101759789498389920 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
