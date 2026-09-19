import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart3_0_certificate :
    ledgerPackedSum highLedgerPart3_0 highLedgerPrepared3 = 19998969841499156794285573184 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
