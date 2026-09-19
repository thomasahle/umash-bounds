import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart12_19_certificate :
    ledgerPackedSum highLedgerPart12_19 highLedgerPrepared12 = 21753035273783080374626399936 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
