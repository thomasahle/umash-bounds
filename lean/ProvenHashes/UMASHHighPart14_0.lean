import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart14_0_certificate :
    ledgerPackedSum highLedgerPart14_0 highLedgerPrepared14 = 19672312878842495115166324512 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
