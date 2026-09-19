import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 480 through 511. -/
theorem highLedgerPart8_15_certificate :
    ledgerPackedSum highLedgerPart8_15 highLedgerPrepared8 = 9917830977312693191857127816 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
