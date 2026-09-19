import ProvenHashes.UMASHHighParts7

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 800 through 831. -/
theorem highLedgerPart7_25_certificate :
    ledgerPackedSum highLedgerPart7_25 highLedgerPrepared7 = 16808403620964882143722922808 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
