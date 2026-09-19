import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart8_3_certificate :
    ledgerPackedSum highLedgerPart8_3 highLedgerPrepared8 = 6746216330408381633702357880 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
