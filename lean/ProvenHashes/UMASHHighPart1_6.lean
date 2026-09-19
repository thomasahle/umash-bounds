import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart1_6_certificate :
    ledgerPackedSum highLedgerPart1_6 highLedgerPrepared1 = 82625230435300044535487231488 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
