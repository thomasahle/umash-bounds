import ProvenHashes.UMASHHighParts5

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 768 through 799. -/
theorem highLedgerPart5_24_certificate :
    ledgerPackedSum highLedgerPart5_24 highLedgerPrepared5 = 22254265254393734267226465920 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
