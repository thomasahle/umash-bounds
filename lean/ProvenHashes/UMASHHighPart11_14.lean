import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart11_14_certificate :
    ledgerPackedSum highLedgerPart11_14 highLedgerPrepared11 = 17405697859334353208352704240 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
