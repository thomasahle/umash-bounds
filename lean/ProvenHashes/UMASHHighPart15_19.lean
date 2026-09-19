import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart15_19_certificate :
    ledgerPackedSum highLedgerPart15_19 highLedgerPrepared15 = 39457829028383955187403993744 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
