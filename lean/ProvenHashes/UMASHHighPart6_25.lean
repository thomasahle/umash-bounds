import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart6_25_certificate :
    ledgerPackedSum highLedgerPart6_25 highLedgerPrepared6 = 11056253174387013102215818032 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
