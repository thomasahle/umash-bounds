import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart14_6_certificate :
    ledgerPackedSum highLedgerPart14_6 highLedgerPrepared14 = 13947503083602766396139001280 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
