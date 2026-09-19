import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart1_26_certificate :
    ledgerPackedSum highLedgerPart1_26 highLedgerPrepared1 = 5823664221069417678526030144 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
