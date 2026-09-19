import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart12_17_certificate :
    ledgerPackedSum highLedgerPart12_17 highLedgerPrepared12 = 16237255122476322585321005440 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
