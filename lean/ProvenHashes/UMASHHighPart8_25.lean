import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart8_25_certificate :
    ledgerPackedSum highLedgerPart8_25 highLedgerPrepared8 = 7353680111024351191589261632 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
