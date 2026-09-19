import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 32 through 63. -/
theorem highLedgerPart12_1_certificate :
    ledgerPackedSum highLedgerPart12_1 highLedgerPrepared12 = 9702859300896031782451978592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
