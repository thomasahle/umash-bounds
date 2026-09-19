import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart1_2_certificate :
    ledgerPackedSum highLedgerPart1_2 highLedgerPrepared1 = 30279511407601040744274018672 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
