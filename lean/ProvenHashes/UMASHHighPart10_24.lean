import ProvenHashes.UMASHHighParts10

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart10_24_certificate :
    ledgerPackedSum highLedgerPart10_24 highLedgerPrepared10 = 16298952868961550031582723264 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
