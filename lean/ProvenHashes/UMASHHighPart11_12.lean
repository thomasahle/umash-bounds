import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 384 through 415. -/
theorem highLedgerPart11_12_certificate :
    ledgerPackedSum highLedgerPart11_12 highLedgerPrepared11 = 17773563434702163901209617632 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
