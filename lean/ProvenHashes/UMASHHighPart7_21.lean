import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 672 through 703. -/
theorem highLedgerPart7_21_certificate :
    ledgerPackedSum highLedgerPart7_21 highLedgerPrepared7 = 13315256883694336900087278304 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
