import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart12_3_certificate :
    ledgerPackedSum highLedgerPart12_3 highLedgerPrepared12 = 11763654333859975829239311416 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
