import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart4_26_certificate :
    ledgerPackedSum highLedgerPart4_26 highLedgerPrepared4 = 9807009944989570790694047072 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
