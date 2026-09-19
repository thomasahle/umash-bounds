import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart13_20_certificate :
    ledgerPackedSum highLedgerPart13_20 highLedgerPrepared13 = 15198920106057380411568641776 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
