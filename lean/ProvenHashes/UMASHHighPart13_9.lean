import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart13_9_certificate :
    ledgerPackedSum highLedgerPart13_9 highLedgerPrepared13 = 24909558195477283470434254672 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
