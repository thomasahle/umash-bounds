import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart3_6_certificate :
    ledgerPackedSum highLedgerPart3_6 highLedgerPrepared3 = 20131150625167657388620491648 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
