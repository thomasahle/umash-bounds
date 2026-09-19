import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 704 through 735. -/
theorem highLedgerPart11_22_certificate :
    ledgerPackedSum highLedgerPart11_22 highLedgerPrepared11 = 16142532229540702758635011968 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
