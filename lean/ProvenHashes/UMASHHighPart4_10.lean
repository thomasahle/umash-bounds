import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 320 through 351. -/
theorem highLedgerPart4_10_certificate :
    ledgerPackedSum highLedgerPart4_10 highLedgerPrepared4 = 16243041363055004430775681024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
