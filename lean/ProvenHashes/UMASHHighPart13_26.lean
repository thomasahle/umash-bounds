import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart13_26_certificate :
    ledgerPackedSum highLedgerPart13_26 highLedgerPrepared13 = 10419645023052903469890065616 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
