import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart4_4_certificate :
    ledgerPackedSum highLedgerPart4_4 highLedgerPrepared4 = 11205251080306223432825009040 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
