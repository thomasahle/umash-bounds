import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart11_3_certificate :
    ledgerPackedSum highLedgerPart11_3 highLedgerPrepared11 = 13365501446457300210998493808 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
