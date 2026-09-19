import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 512 through 543. -/
theorem highLedgerPart10_16_certificate :
    ledgerPackedSum highLedgerPart10_16 highLedgerPrepared10 = 15928861037056573653071482176 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
