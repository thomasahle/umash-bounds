import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart12_26_certificate :
    ledgerPackedSum highLedgerPart12_26 highLedgerPrepared12 = 9366056842211470984726160336 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
