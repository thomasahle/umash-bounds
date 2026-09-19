import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart14_7_certificate :
    ledgerPackedSum highLedgerPart14_7 highLedgerPrepared14 = 18739044775563707079568232304 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
