import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart12_16_certificate :
    ledgerPackedSum highLedgerPart12_16 highLedgerPrepared12 = 15354044191110524393936280160 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
