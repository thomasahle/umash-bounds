import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart14_23_certificate :
    ledgerPackedSum highLedgerPart14_23 highLedgerPrepared14 = 16245905179541729672114153824 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
