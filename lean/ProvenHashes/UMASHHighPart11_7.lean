import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart11_7_certificate :
    ledgerPackedSum highLedgerPart11_7 highLedgerPrepared11 = 14445376892242528507840088080 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
