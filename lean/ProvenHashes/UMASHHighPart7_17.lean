import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart7_17_certificate :
    ledgerPackedSum highLedgerPart7_17 highLedgerPrepared7 = 16687626921465764615231006592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
