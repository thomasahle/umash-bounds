import ProvenHashes.UMASHHighParts9

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart9_24_certificate :
    ledgerPackedSum highLedgerPart9_24 highLedgerPrepared9 = 10284210610677387993708101664 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
