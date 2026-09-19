import ProvenHashes.UMASHHighParts15

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart15_24_certificate :
    ledgerPackedSum highLedgerPart15_24 highLedgerPrepared15 = 17530120016042438276543661784 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
