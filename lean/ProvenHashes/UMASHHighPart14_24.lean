import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart14_24_certificate :
    ledgerPackedSum highLedgerPart14_24 highLedgerPrepared14 = 19139207726161557759286766608 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
