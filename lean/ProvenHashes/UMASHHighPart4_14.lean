import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart4_14_certificate :
    ledgerPackedSum highLedgerPart4_14 highLedgerPrepared4 = 16284603070063075056613349216 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
