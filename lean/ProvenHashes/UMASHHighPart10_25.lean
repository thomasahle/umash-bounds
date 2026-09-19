import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart10_25_certificate :
    ledgerPackedSum highLedgerPart10_25 highLedgerPrepared10 = 21983936449105825938474294928 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
