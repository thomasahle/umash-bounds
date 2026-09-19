import ProvenHashes.UMASHMaskCensus3125

namespace ProvenHashes.UMASH
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem liftingClasses_card_58 : (liftingClasses 58).card = 26*58-75 := by
  rw [liftingClasses_card_formula]
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
