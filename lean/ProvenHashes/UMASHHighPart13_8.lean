import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart13_8_certificate :
    ledgerPackedSum highLedgerPart13_8 highLedgerPrepared13 = 17497827149106408885819186784 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
