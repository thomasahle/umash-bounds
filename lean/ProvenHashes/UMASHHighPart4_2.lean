import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart4_2_certificate :
    ledgerPackedSum highLedgerPart4_2 highLedgerPrepared4 = 11783404862371386658445049664 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
