import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart12_7_certificate :
    ledgerPackedSum highLedgerPart12_7 highLedgerPrepared12 = 12547924325766180964700756144 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
