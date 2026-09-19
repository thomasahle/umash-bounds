import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart3_2_certificate :
    ledgerPackedSum highLedgerPart3_2 highLedgerPrepared3 = 20766607319745676148563258336 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
