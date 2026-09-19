import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart7_4_certificate :
    ledgerPackedSum highLedgerPart7_4 highLedgerPrepared7 = 11404898405458951979193345424 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
