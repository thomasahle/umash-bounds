import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart8_4_certificate :
    ledgerPackedSum highLedgerPart8_4 highLedgerPrepared8 = 7642839219255110680216398384 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
