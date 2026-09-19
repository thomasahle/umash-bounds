import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart14_13_certificate :
    ledgerPackedSum highLedgerPart14_13 highLedgerPrepared14 = 20211366056285444616524584512 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
