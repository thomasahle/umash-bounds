import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart9_5_certificate :
    ledgerPackedSum highLedgerPart9_5 highLedgerPrepared9 = 7590768596755444924435194784 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
