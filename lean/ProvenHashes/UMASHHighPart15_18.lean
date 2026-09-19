import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart15_18_certificate :
    ledgerPackedSum highLedgerPart15_18 highLedgerPrepared15 = 17138408183766115579280017456 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
