import ProvenHashes.UMASHHighParts1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 608 through 639. -/
theorem highLedgerPart1_19_certificate :
    ledgerPackedSum highLedgerPart1_19 highLedgerPrepared1 = 1233986814812542752086873280 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
