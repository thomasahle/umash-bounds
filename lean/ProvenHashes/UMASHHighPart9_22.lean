import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart9_22_certificate :
    ledgerPackedSum highLedgerPart9_22 highLedgerPrepared9 = 11690368340597789076121166880 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
