import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart3_19_certificate :
    ledgerPackedSum highLedgerPart3_19 highLedgerPrepared3 = 29619456874317046900420303104 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
