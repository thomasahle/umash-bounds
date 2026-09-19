import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart9_8_certificate :
    ledgerPackedSum highLedgerPart9_8 highLedgerPrepared9 = 13317317892797514844056406688 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
