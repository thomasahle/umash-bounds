import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart8_8_certificate :
    ledgerPackedSum highLedgerPart8_8 highLedgerPrepared8 = 16542057794333788904546244288 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
