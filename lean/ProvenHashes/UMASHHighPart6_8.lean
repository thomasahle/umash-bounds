import ProvenHashes.UMASHHighParts6

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 256 through 287. -/
theorem highLedgerPart6_8_certificate :
    ledgerPackedSum highLedgerPart6_8 highLedgerPrepared6 = 14424520499952972777496323776 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
