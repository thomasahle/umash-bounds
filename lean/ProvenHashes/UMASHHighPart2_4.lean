import ProvenHashes.UMASHHighParts2

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart2_4_certificate :
    ledgerPackedSum highLedgerPart2_4 highLedgerPrepared2 = 98226305170408316045534327936 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
