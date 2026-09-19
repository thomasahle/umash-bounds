import ProvenHashes.UMASHHighParts3

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 224 through 255. -/
theorem highLedgerPart3_7_certificate :
    ledgerPackedSum highLedgerPart3_7 highLedgerPrepared3 = 23652494728574981684923710816 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
