import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart7_20_certificate :
    ledgerPackedSum highLedgerPart7_20 highLedgerPrepared7 = 13521230158419142082348734016 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
