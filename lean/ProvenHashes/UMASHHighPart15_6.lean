import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart15_6_certificate :
    ledgerPackedSum highLedgerPart15_6 highLedgerPrepared15 = 12452731287863436258415400160 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
