import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart12_4_certificate :
    ledgerPackedSum highLedgerPart12_4 highLedgerPrepared12 = 13278146319312650013978996016 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
