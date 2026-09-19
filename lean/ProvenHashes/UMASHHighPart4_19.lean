import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart4_19_certificate :
    ledgerPackedSum highLedgerPart4_19 highLedgerPrepared4 = 16482074523604589980910226240 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
