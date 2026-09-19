import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart4_5_certificate :
    ledgerPackedSum highLedgerPart4_5 highLedgerPrepared4 = 11019848491100675185210203648 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
