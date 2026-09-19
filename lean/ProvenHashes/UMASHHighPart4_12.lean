import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart4_12_certificate :
    ledgerPackedSum highLedgerPart4_12 highLedgerPrepared4 = 15286533424256416818474542944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
