import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart14_8_certificate :
    ledgerPackedSum highLedgerPart14_8 highLedgerPrepared14 = 16008119058645023214023598208 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
