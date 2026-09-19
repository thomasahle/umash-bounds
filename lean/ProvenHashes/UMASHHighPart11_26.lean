import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart11_26_certificate :
    ledgerPackedSum highLedgerPart11_26 highLedgerPrepared11 = 9441804699966572532466816624 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
