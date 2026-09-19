import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart7_16_certificate :
    ledgerPackedSum highLedgerPart7_16 highLedgerPrepared7 = 13710706732122262197442166624 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
