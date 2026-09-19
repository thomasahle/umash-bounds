import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart12_14_certificate :
    ledgerPackedSum highLedgerPart12_14 highLedgerPrepared12 = 13525935501670953987323474416 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
