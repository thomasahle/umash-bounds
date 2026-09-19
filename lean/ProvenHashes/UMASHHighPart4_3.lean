import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart4_3_certificate :
    ledgerPackedSum highLedgerPart4_3 highLedgerPrepared4 = 11739288062344355088488268744 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
