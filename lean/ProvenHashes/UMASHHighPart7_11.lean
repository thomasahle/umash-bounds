import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 352 through 383. -/
theorem highLedgerPart7_11_certificate :
    ledgerPackedSum highLedgerPart7_11 highLedgerPrepared7 = 13421854513211212450593617248 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
