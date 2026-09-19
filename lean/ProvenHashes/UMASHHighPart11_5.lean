import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart11_5_certificate :
    ledgerPackedSum highLedgerPart11_5 highLedgerPrepared11 = 11723814224544587545681026112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
