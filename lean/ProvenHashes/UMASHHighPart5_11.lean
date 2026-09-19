import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart5_11_certificate :
    ledgerPackedSum highLedgerPart5_11 highLedgerPrepared5 = 17627341637386329404183861056 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
