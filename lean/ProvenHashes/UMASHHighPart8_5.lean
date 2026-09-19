import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart8_5_certificate :
    ledgerPackedSum highLedgerPart8_5 highLedgerPrepared8 = 9699290304052228263728315456 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
