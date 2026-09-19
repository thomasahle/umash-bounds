import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart12_25_certificate :
    ledgerPackedSum highLedgerPart12_25 highLedgerPrepared12 = 14104964929444445033170841072 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
