import ProvenHashes.UMASHLowWeightSix
import ProvenHashes.UMASHJointLedgerLowFinal

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet lowTargetK phenhENHMask

theorem phenh_low_ledger_lt91 (r s : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hs1 : 1 ≤ s) (hs15 : s ≤ 15) :
    phenhLowLedger r s/q^2 < (1:ℚ≥0)/2^91 := by
  have hbound : phenhLowLedger r s ≤ 101418270720 := by
    interval_cases r
    · have hC : ∀ e, lowTargetK 1 e ≤ 34078720 :=
        fun e => lowTargetK_small_valuation_le (0:Fin 2) e
      exact (phenh_low_ledger_uniform_bound 1 s 34078720 6 hC twist_low_weight_sum_six).trans
        (by norm_num [valuationMasks_card_table.2.1])
    · have hC : ∀ e, lowTargetK 2 e ≤ 67108864 :=
        fun e => lowTargetK_small_valuation_le (1:Fin 2) e
      have hW : (∑ v ∈ valuationMasks 2, twistLowWeight v) ≤ 4 :=
        (Finset.sum_le_sum (fun v _ => twistLowWeight_le_popcount v)).trans
          twist_low_popcount_sum_certificate.2
      exact (phenh_low_ledger_uniform_bound 2 s 67108864 4 hC hW).trans
        (by norm_num [valuationMasks_card_table.2.2.1])
    · have h := phenh_low_ledger_r3_certificate ⟨s-1,by omega⟩
      simpa only [show s-1+1 = s by omega] using h.trans (by norm_num : (268435521:ℚ≥0) ≤ 101418270720)
  exact (div_le_div_of_nonneg_right hbound (by positivity)).trans_lt
    (by apply NNRat.coe_lt_coe.mp; norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
