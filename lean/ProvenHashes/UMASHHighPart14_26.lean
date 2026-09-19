import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 832 through 851. -/
theorem highLedgerPart14_26_certificate :
    ledgerPackedSum highLedgerPart14_26 highLedgerPrepared14 = 10647993178079550714153443248 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
