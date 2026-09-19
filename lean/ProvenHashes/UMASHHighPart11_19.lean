import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart11_19_certificate :
    ledgerPackedSum highLedgerPart11_19 highLedgerPrepared11 = 21438508426830042093440474640 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
