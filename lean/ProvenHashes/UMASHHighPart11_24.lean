import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart11_24_certificate :
    ledgerPackedSum highLedgerPart11_24 highLedgerPrepared11 = 15647378790821736802090929328 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
