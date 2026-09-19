import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart7_14_certificate :
    ledgerPackedSum highLedgerPart7_14 highLedgerPrepared7 = 17924303890531814073108687472 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
