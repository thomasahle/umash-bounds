import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart8_16_certificate :
    ledgerPackedSum highLedgerPart8_16 highLedgerPrepared8 = 13122167278912958173584153120 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
