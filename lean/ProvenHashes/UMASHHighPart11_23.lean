import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart11_23_certificate :
    ledgerPackedSum highLedgerPart11_23 highLedgerPrepared11 = 17340603042106071033151658528 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
