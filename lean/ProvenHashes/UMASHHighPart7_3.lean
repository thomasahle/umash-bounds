import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart7_3_certificate :
    ledgerPackedSum highLedgerPart7_3 highLedgerPrepared7 = 13018554854639880352845487120 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
