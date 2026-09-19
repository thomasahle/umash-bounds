import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart6_24_certificate :
    ledgerPackedSum highLedgerPart6_24 highLedgerPrepared6 = 15171722022637623281458150784 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
