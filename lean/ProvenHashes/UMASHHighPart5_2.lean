import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 64 through 95. -/
theorem highLedgerPart5_2_certificate :
    ledgerPackedSum highLedgerPart5_2 highLedgerPrepared5 = 16196477077485751560427964416 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
