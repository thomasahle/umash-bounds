import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart3_1_certificate :
    ledgerPackedSum highLedgerPart3_1 highLedgerPrepared3 = 20061044387282994626500902320 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
