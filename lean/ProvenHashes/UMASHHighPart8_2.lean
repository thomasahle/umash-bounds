import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart8_2_certificate :
    ledgerPackedSum highLedgerPart8_2 highLedgerPrepared8 = 9326263535402605613717709184 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
