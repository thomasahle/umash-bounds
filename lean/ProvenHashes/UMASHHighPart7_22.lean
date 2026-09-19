import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart7_22_certificate :
    ledgerPackedSum highLedgerPart7_22 highLedgerPrepared7 = 14581665758997596665690706688 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
