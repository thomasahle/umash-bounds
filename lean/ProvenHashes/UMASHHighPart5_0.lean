import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart5_0_certificate :
    ledgerPackedSum highLedgerPart5_0 highLedgerPrepared5 = 14626239126883538040672316736 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
