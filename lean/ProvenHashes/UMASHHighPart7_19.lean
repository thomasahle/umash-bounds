import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart7_19_certificate :
    ledgerPackedSum highLedgerPart7_19 highLedgerPrepared7 = 18470963097760735867138944480 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
