import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart11_2_certificate :
    ledgerPackedSum highLedgerPart11_2 highLedgerPrepared11 = 13045481272195161777213269344 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
