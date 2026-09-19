import ProvenHashes.UMASHJointLedgerCertificate

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] maskSet

/-- A 130-case exact-rational certificate for the dense/quadratic minimum.
It depends only on the popcount, not on a shuffler or a raw-mask pair. -/
theorem low_target_ceiling_certificate : ∀ (r : Fin 2) (h : Fin 65),
    min ((65:ℚ≥0)*2^(64-h.val)) (4*2^(r.val+1)*2^((h.val+1)/2)) ≤
      if r.val = 0 then 34078720 else 67108864 := by
  decide +kernel
-- CHECKPOINT

/-- Uniform target ceilings remove the need to enumerate low mask pairs. -/
theorem lowTargetK_small_valuation_le (r : Fin 2) (e : ℕ) :
    lowTargetK (r.val+1) e ≤ if r.val = 0 then 34078720 else 67108864 := by
  by_cases he : e = 0
  · subst e
    simp only [lowTargetK, ↓reduceIte]
    fin_cases r <;> norm_num
  · rw [lowTargetK, if_neg he]
    exact (min_le_right _ _).trans
      (low_target_ceiling_certificate r ⟨(maskBitSet 64 e).card, by
        have := mask_bit_set_card_le 64 e
        omega⟩)
-- CHECKPOINT

end ProvenHashes.UMASH
