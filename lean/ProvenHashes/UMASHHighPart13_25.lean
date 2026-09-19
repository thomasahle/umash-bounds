import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart13_25_certificate :
    ledgerPackedSum highLedgerPart13_25 highLedgerPrepared13 = 15408123422962859710571434768 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
