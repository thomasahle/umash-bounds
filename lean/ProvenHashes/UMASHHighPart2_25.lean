import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart2_25_certificate :
    ledgerPackedSum highLedgerPart2_25 highLedgerPrepared2 = 130171597513401884086370789664 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
