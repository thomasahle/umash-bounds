import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart7_8_certificate :
    ledgerPackedSum highLedgerPart7_8 highLedgerPrepared7 = 15157669573448266354276325280 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
