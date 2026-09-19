import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 160 through 191. -/
theorem highLedgerPart13_5_certificate :
    ledgerPackedSum highLedgerPart13_5 highLedgerPrepared13 = 10539054275516082056858582624 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
