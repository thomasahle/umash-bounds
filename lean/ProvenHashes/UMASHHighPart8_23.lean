import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 736 through 767. -/
theorem highLedgerPart8_23_certificate :
    ledgerPackedSum highLedgerPart8_23 highLedgerPrepared8 = 11694951949356565361548087616 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
