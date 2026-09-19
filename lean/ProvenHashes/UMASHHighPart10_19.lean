import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart10_19_certificate :
    ledgerPackedSum highLedgerPart10_19 highLedgerPrepared10 = 23891373623773378446024607952 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
