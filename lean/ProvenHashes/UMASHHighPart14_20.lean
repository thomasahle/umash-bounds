import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart14_20_certificate :
    ledgerPackedSum highLedgerPart14_20 highLedgerPrepared14 = 18162175794777946348930460864 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
