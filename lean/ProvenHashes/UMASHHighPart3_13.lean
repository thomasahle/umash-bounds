import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart3_13_certificate :
    ledgerPackedSum highLedgerPart3_13 highLedgerPrepared3 = 28513215601943332254146420000 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
