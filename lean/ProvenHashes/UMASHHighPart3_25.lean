import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart3_25_certificate :
    ledgerPackedSum highLedgerPart3_25 highLedgerPrepared3 = 29137152388296278733253780608 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
