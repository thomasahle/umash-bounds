import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart15_3_certificate :
    ledgerPackedSum highLedgerPart15_3 highLedgerPrepared15 = 15596817156844935950711283728 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
