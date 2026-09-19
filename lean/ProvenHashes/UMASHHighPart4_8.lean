import ProvenHashes.UMASHHighParts4

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart4_8_certificate :
    ledgerPackedSum highLedgerPart4_8 highLedgerPrepared4 = 16400745537349217891867802880 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
