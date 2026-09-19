import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart13_2_certificate :
    ledgerPackedSum highLedgerPart13_2 highLedgerPrepared13 = 13023309320122073781903495968 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
