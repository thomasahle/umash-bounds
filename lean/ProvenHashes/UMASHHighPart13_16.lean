import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart13_16_certificate :
    ledgerPackedSum highLedgerPart13_16 highLedgerPrepared13 = 17408917662230875540487518240 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
