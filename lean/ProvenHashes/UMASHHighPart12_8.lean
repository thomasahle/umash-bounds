import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart12_8_certificate :
    ledgerPackedSum highLedgerPart12_8 highLedgerPrepared12 = 16438328037736215983442120960 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
