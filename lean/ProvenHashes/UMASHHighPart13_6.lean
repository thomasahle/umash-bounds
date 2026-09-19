import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart13_6_certificate :
    ledgerPackedSum highLedgerPart13_6 highLedgerPrepared13 = 10605033821889705641979160096 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
