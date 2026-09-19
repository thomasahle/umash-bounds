import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart15_8_certificate :
    ledgerPackedSum highLedgerPart15_8 highLedgerPrepared15 = 16608685019871734360798317632 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
