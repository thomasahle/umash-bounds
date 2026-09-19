import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart7_18_certificate :
    ledgerPackedSum highLedgerPart7_18 highLedgerPrepared7 = 16716035887036358479826834768 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
