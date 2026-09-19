import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart9_25_certificate :
    ledgerPackedSum highLedgerPart9_25 highLedgerPrepared9 = 7195219607754694535094711016 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
