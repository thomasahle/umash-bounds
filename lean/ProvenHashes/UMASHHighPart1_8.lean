import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart1_8_certificate :
    ledgerPackedSum highLedgerPart1_8 highLedgerPrepared1 = 70209502760842323044103885024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
