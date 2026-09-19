import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 192 through 223. -/
theorem highLedgerPart8_6_certificate :
    ledgerPackedSum highLedgerPart8_6 highLedgerPrepared8 = 7164319461434135083032681824 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
