import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart9_17_certificate :
    ledgerPackedSum highLedgerPart9_17 highLedgerPrepared9 = 11486816728191687485041131264 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
