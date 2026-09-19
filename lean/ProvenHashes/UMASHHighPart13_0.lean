import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 0 through 31. -/
theorem highLedgerPart13_0_certificate :
    ledgerPackedSum highLedgerPart13_0 highLedgerPrepared13 = 14947517972324077798889974304 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
