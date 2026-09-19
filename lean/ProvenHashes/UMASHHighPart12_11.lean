import ProvenHashes.UMASHHighParts12

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart12_11_certificate :
    ledgerPackedSum highLedgerPart12_11 highLedgerPrepared12 = 14748711290507677292149547008 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
