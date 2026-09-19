import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart13_14_certificate :
    ledgerPackedSum highLedgerPart13_14 highLedgerPrepared13 = 13990191756352168203955024112 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
