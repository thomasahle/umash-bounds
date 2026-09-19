import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart13_10_certificate :
    ledgerPackedSum highLedgerPart13_10 highLedgerPrepared13 = 18517506488163465934734365120 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
