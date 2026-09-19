import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart8_9_certificate :
    ledgerPackedSum highLedgerPart8_9 highLedgerPrepared8 = 9487487356704042055964959416 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
