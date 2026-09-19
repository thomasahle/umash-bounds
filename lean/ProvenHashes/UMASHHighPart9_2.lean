import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart9_2_certificate :
    ledgerPackedSum highLedgerPart9_2 highLedgerPrepared9 = 8498870795214177960068837120 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
