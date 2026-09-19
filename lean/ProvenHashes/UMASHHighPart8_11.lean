import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart8_11_certificate :
    ledgerPackedSum highLedgerPart8_11 highLedgerPrepared8 = 12840773035772819087537162080 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
