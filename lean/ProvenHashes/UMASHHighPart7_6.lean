import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart7_6_certificate :
    ledgerPackedSum highLedgerPart7_6 highLedgerPrepared7 = 13560201715703349265050514080 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
