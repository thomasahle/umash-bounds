import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart1_22_certificate :
    ledgerPackedSum highLedgerPart1_22 highLedgerPrepared1 = 69519161116982614950935685920 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
