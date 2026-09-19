import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart1_4_certificate :
    ledgerPackedSum highLedgerPart1_4 highLedgerPrepared1 = 565616223020586101383396672 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
