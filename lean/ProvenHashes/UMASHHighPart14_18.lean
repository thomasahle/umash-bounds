import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 576 through 607. -/
theorem highLedgerPart14_18_certificate :
    ledgerPackedSum highLedgerPart14_18 highLedgerPrepared14 = 17346399009896133823865956704 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
