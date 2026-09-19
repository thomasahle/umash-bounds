import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart13_11_certificate :
    ledgerPackedSum highLedgerPart13_11 highLedgerPrepared13 = 14604062859526625465976664608 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
