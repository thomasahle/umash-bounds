import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart13_4_certificate :
    ledgerPackedSum highLedgerPart13_4 highLedgerPrepared13 = 14739186876081817711749345456 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
