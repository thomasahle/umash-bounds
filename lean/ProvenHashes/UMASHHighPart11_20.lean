import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart11_20_certificate :
    ledgerPackedSum highLedgerPart11_20 highLedgerPrepared11 = 14720159290369045035523057616 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
