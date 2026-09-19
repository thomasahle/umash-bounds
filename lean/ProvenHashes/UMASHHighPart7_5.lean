import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart7_5_certificate :
    ledgerPackedSum highLedgerPart7_5 highLedgerPrepared7 = 9917000196582066694606134336 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
