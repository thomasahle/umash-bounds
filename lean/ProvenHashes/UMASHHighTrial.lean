import ProvenHashes.UMASHHighData1

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem highLedger_first_row_certificate :
    ledgerSum (highLedgerData1.take 1) highLedgerData1 = 317495379360192438446624 := by
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
