import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart4_6_certificate :
    ledgerPackedSum highLedgerPart4_6 highLedgerPrepared4 = 11123010546212620403531474208 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
