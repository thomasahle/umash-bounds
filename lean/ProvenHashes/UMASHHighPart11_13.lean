import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart11_13_certificate :
    ledgerPackedSum highLedgerPart11_13 highLedgerPrepared11 = 16657623329073254297471383136 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
