import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart1_11_certificate :
    ledgerPackedSum highLedgerPart1_11 highLedgerPrepared1 = 8058436836845053047236908488 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
