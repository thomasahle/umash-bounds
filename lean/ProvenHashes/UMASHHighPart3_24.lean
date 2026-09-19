import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart3_24_certificate :
    ledgerPackedSum highLedgerPart3_24 highLedgerPrepared3 = 27467768238748358160653317856 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
