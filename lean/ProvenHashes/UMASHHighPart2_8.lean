import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart2_8_certificate :
    ledgerPackedSum highLedgerPart2_8 highLedgerPrepared2 = 117826927176330691543809765856 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
