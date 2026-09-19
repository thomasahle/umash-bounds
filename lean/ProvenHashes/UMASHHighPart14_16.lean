import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart14_16_certificate :
    ledgerPackedSum highLedgerPart14_16 highLedgerPrepared14 = 16869929672924935847902802016 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
