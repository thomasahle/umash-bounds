import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart3_4_certificate :
    ledgerPackedSum highLedgerPart3_4 highLedgerPrepared3 = 20618268371707779791564800832 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
