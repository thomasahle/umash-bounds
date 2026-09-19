import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart1_25_certificate :
    ledgerPackedSum highLedgerPart1_25 highLedgerPrepared1 = 16276723914959446972678337440 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
