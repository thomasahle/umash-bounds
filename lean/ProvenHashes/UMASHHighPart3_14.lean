import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart3_14_certificate :
    ledgerPackedSum highLedgerPart3_14 highLedgerPrepared3 = 30070639486997804812175867504 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
