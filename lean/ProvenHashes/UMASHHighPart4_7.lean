import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart4_7_certificate :
    ledgerPackedSum highLedgerPart4_7 highLedgerPrepared4 = 12918947152663145135050902592 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
