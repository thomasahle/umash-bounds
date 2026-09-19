import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart4_24_certificate :
    ledgerPackedSum highLedgerPart4_24 highLedgerPrepared4 = 14841837032132992585421546848 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
