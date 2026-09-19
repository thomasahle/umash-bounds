import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart4_0_certificate :
    ledgerPackedSum highLedgerPart4_0 highLedgerPrepared4 = 10691144846765030647486856704 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
