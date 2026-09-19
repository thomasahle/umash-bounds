import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart13_19_certificate :
    ledgerPackedSum highLedgerPart13_19 highLedgerPrepared13 = 26367461736048792615193301872 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
