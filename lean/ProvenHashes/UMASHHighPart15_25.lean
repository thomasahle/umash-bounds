import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart15_25_certificate :
    ledgerPackedSum highLedgerPart15_25 highLedgerPrepared15 = 17613144933307108175105551776 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
