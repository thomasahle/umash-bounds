import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart8_19_certificate :
    ledgerPackedSum highLedgerPart8_19 highLedgerPrepared8 = 10395292824102854880842994560 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
