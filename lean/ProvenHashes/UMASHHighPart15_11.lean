import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart15_11_certificate :
    ledgerPackedSum highLedgerPart15_11 highLedgerPrepared15 = 16600711412754822803568640096 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
