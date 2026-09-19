import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart2_24_certificate :
    ledgerPackedSum highLedgerPart2_24 highLedgerPrepared2 = 116788441596686814572046313632 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
