import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart11_17_certificate :
    ledgerPackedSum highLedgerPart11_17 highLedgerPrepared11 = 16921768674307010827379064224 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
