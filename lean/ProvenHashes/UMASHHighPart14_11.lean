import ProvenHashes.UMASHHighParts14

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart14_11_certificate :
    ledgerPackedSum highLedgerPart14_11 highLedgerPrepared14 = 14886507674138878509183217376 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
