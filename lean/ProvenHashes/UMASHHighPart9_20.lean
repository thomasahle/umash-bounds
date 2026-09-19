import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart9_20_certificate :
    ledgerPackedSum highLedgerPart9_20 highLedgerPrepared9 = 11073775942007921171463056112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
