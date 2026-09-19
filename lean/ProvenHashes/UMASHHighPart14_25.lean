import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart14_25_certificate :
    ledgerPackedSum highLedgerPart14_25 highLedgerPrepared14 = 18047080665725039003983559424 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
