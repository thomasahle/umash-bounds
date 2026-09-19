import ProvenHashes.UMASHHighParts8

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 640 through 671. -/
theorem highLedgerPart8_20_certificate :
    ledgerPackedSum highLedgerPart8_20 highLedgerPrepared8 = 11406821756866530668783635680 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
