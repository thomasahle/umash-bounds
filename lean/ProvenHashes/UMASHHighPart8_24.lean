import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart8_24_certificate :
    ledgerPackedSum highLedgerPart8_24 highLedgerPrepared8 = 10689420609967635820663243200 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
