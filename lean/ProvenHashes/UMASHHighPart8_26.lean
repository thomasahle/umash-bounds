import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart8_26_certificate :
    ledgerPackedSum highLedgerPart8_26 highLedgerPrepared8 = 4113603890442718557423287088 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
