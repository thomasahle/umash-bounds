import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart14_4_certificate :
    ledgerPackedSum highLedgerPart14_4 highLedgerPrepared14 = 19310810510712672153646766960 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
