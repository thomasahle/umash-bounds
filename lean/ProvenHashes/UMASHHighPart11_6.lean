import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart11_6_certificate :
    ledgerPackedSum highLedgerPart11_6 highLedgerPrepared11 = 12624077691551374334744214336 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
