import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart13_24_certificate :
    ledgerPackedSum highLedgerPart13_24 highLedgerPrepared13 = 15750525027068348244035675224 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
