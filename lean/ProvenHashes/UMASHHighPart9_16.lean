import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart9_16_certificate :
    ledgerPackedSum highLedgerPart9_16 highLedgerPrepared9 = 12779364587613439225727865024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
