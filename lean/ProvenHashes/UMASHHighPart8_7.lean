import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart8_7_certificate :
    ledgerPackedSum highLedgerPart8_7 highLedgerPrepared8 = 5346786581322953256610519568 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
