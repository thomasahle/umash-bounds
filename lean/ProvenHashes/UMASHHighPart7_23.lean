import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart7_23_certificate :
    ledgerPackedSum highLedgerPart7_23 highLedgerPrepared7 = 16176985278896568785061554432 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
