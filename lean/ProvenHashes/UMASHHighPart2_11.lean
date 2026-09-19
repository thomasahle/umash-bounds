import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart2_11_certificate :
    ledgerPackedSum highLedgerPart2_11 highLedgerPrepared2 = 117622322384724559248199291232 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
