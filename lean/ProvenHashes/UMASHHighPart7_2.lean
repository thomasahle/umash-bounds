import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart7_2_certificate :
    ledgerPackedSum highLedgerPart7_2 highLedgerPrepared7 = 11048915841032508214696692768 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
