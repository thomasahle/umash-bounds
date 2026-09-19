import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart1_20_certificate :
    ledgerPackedSum highLedgerPart1_20 highLedgerPrepared1 = 295161773205368424593377408 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
