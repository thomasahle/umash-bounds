import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart15_7_certificate :
    ledgerPackedSum highLedgerPart15_7 highLedgerPrepared15 = 18859969963705469461522683600 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
