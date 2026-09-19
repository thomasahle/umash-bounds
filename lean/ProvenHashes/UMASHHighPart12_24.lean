import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart12_24_certificate :
    ledgerPackedSum highLedgerPart12_24 highLedgerPrepared12 = 14105297772569435411522078448 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
