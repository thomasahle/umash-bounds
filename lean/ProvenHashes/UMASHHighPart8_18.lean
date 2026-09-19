import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart8_18_certificate :
    ledgerPackedSum highLedgerPart8_18 highLedgerPrepared8 = 9289029888437739394363665248 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
