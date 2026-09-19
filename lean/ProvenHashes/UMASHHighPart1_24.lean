import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart1_24_certificate :
    ledgerPackedSum highLedgerPart1_24 highLedgerPrepared1 = 58784174311209525466638036448 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
