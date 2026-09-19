import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart11_18_certificate :
    ledgerPackedSum highLedgerPart11_18 highLedgerPrepared11 = 15782473411412400761456044112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
