import ProvenHashes.UMASHHighParts13

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Exact integer sum of rows 96 through 127. -/
theorem highLedgerPart13_3_certificate :
    ledgerPackedSum highLedgerPart13_3 highLedgerPrepared13 = 13562232066916732166225301088 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
