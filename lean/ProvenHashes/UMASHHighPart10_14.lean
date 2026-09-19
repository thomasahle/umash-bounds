import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 448 through 479. -/
theorem highLedgerPart10_14_certificate :
    ledgerPackedSum highLedgerPart10_14 highLedgerPrepared10 = 23794446145740749048259617024 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
