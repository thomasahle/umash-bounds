import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart7_24_certificate :
    ledgerPackedSum highLedgerPart7_24 highLedgerPrepared7 = 18510425767817231772780217536 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
