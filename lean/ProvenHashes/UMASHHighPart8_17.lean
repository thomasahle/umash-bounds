import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart8_17_certificate :
    ledgerPackedSum highLedgerPart8_17 highLedgerPrepared8 = 13264497545975976384660677888 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
