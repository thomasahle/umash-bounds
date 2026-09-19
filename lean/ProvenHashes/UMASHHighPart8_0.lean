import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart8_0_certificate :
    ledgerPackedSum highLedgerPart8_0 highLedgerPrepared8 = 7893503628148845308087818560 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
