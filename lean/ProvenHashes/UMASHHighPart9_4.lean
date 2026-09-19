import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart9_4_certificate :
    ledgerPackedSum highLedgerPart9_4 highLedgerPrepared9 = 7092653432098293669398610224 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
