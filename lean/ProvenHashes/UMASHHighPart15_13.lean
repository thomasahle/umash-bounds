import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart15_13_certificate :
    ledgerPackedSum highLedgerPart15_13 highLedgerPrepared15 = 17888003200239591245556177328 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
