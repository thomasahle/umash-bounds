import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 416 through 447. -/
theorem highLedgerPart4_13_certificate :
    ledgerPackedSum highLedgerPart4_13 highLedgerPrepared4 = 15614682891889158254033804832 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
