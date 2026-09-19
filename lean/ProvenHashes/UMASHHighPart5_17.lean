import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 544 through 575. -/
theorem highLedgerPart5_17_certificate :
    ledgerPackedSum highLedgerPart5_17 highLedgerPrepared5 = 21451767470747076027905247968 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
