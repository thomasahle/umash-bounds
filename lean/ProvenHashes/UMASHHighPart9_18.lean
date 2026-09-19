import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart9_18_certificate :
    ledgerPackedSum highLedgerPart9_18 highLedgerPrepared9 = 8724672642392793230481265776 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
