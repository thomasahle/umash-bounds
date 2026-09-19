import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart8_21_certificate :
    ledgerPackedSum highLedgerPart8_21 highLedgerPrepared8 = 11851300759567048580282410368 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
