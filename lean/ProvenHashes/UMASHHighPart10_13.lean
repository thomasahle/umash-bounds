import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart10_13_certificate :
    ledgerPackedSum highLedgerPart10_13 highLedgerPrepared10 = 17795195737728507308876011168 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
