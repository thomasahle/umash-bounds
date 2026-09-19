import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart8_14_certificate :
    ledgerPackedSum highLedgerPart8_14 highLedgerPrepared8 = 7021282331400021218988830064 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
