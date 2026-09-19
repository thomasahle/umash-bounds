import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart15_4_certificate :
    ledgerPackedSum highLedgerPart15_4 highLedgerPrepared15 = 20964754203962163504115235856 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
