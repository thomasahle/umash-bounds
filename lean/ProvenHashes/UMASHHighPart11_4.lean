import ProvenHashes.UMASHHighParts11

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 128 through 159. -/
theorem highLedgerPart11_4_certificate :
    ledgerPackedSum highLedgerPart11_4 highLedgerPrepared11 = 13430313329836867040077800880 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
