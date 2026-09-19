import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart4_23_certificate :
    ledgerPackedSum highLedgerPart4_23 highLedgerPrepared4 = 16100201662123483222991036448 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
