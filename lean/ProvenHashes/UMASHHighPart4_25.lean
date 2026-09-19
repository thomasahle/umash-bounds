import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart4_25_certificate :
    ledgerPackedSum highLedgerPart4_25 highLedgerPrepared4 = 16523198308612006122836860944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
