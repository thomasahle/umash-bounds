import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart9_3_certificate :
    ledgerPackedSum highLedgerPart9_3 highLedgerPrepared9 = 6800743859253750166227886880 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
