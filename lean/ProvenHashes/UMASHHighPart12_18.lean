import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart12_18_certificate :
    ledgerPackedSum highLedgerPart12_18 highLedgerPrepared12 = 14768483201991875335107103808 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
