import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart2_16_certificate :
    ledgerPackedSum highLedgerPart2_16 highLedgerPrepared2 = 120396070752664924486222889888 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
