import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart2_14_certificate :
    ledgerPackedSum highLedgerPart2_14 highLedgerPrepared2 = 130830657872277983351091748352 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
