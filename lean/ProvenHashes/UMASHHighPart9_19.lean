import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart9_19_certificate :
    ledgerPackedSum highLedgerPart9_19 highLedgerPrepared9 = 11513670450777063958449435664 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
