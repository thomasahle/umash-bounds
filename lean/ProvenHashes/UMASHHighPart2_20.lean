import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart2_20_certificate :
    ledgerPackedSum highLedgerPart2_20 highLedgerPrepared2 = 118228009201542171308533255680 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
