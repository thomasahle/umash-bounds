import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart2_19_certificate :
    ledgerPackedSum highLedgerPart2_19 highLedgerPrepared2 = 149174438709539540879259939968 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
