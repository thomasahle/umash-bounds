import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart13_13_certificate :
    ledgerPackedSum highLedgerPart13_13 highLedgerPrepared13 = 17046735138993571379936963824 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
