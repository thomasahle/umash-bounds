import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart12_5_certificate :
    ledgerPackedSum highLedgerPart12_5 highLedgerPrepared12 = 10750040854072132926931983008 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
