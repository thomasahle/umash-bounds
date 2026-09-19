import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 288 through 319. -/
theorem highLedgerPart11_9_certificate :
    ledgerPackedSum highLedgerPart11_9 highLedgerPrepared11 = 20258399173314140022559374944 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
