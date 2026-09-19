import ProvenHashes.UMASHJointLedgerLowPopcount
import ProvenHashes.UMASHLowWeightCertificate

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet lowTargetK phenhENHMask

/-- All thirty r=1,2 numerical cases are bounded uniformly in the shuffler.
The resulting ceilings are 169030451200 and 68719476736, both below C. -/
theorem phenh_low_ledger_small_certificate (r s : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) :
    phenhLowLedger r s ≤ 170906186782 := by
  have hW1 : (∑ v ∈ valuationMasks 1, twistLowWeight v) ≤ 10 :=
    (Finset.sum_le_sum (fun v _ => twistLowWeight_le_popcount v)).trans
      twist_low_popcount_sum_certificate.1
  have hW2 : (∑ v ∈ valuationMasks 2, twistLowWeight v) ≤ 4 :=
    (Finset.sum_le_sum (fun v _ => twistLowWeight_le_popcount v)).trans
      twist_low_popcount_sum_certificate.2
  interval_cases r
  · have hC : ∀ e, lowTargetK 1 e ≤ 34078720 := by
      intro e
      exact lowTargetK_small_valuation_le (0 : Fin 2) e
    exact (phenh_low_ledger_uniform_bound 1 s 34078720 10 hC hW1).trans
      (by norm_num [valuationMasks_card_table.2.1])
  · have hC : ∀ e, lowTargetK 2 e ≤ 67108864 := by
      intro e
      exact lowTargetK_small_valuation_le (1 : Fin 2) e
    exact (phenh_low_ledger_uniform_bound 2 s 67108864 4 hC hW2).trans
      (by norm_num [valuationMasks_card_table.2.2.1])
-- CHECKPOINT

/-- The full 45-case low portion of the PROOF2 certificate is closed. -/
theorem phenh_low_ledger_certificate (r s : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hs1 : 1 ≤ s) (hs15 : s ≤ 15) : phenhLowLedger r s ≤ 170906186782 := by
  by_cases h3 : r = 3
  · subst r
    have h := phenh_low_ledger_r3_certificate ⟨s-1, by omega⟩
    have hh : (s-1)+1 = s := by omega
    simp only [hh] at h
    exact h.trans (by norm_num)
  · exact phenh_low_ledger_small_certificate r s hr1 (by omega)
-- CHECKPOINT

/-- Only the fifteen high-ledger computations remain in the full certificate. -/
theorem phenh_joint_ledger_certificate_of_high
    (hhigh : ∀ s : ℕ, 1 ≤ s → s ≤ 15 → phenhHighLedger s ≤ 170906186782) :
    PHENHJointLedgerCertificate := ⟨phenh_low_ledger_certificate, hhigh⟩
-- CHECKPOINT

/-- The sharp literal-block theorem now needs only the fifteen explicit
high-ledger inequalities; the probabilistic reduction has no remaining premise. -/
theorem joint_phenh_sharp_of_high_ledger
    (hhigh : ∀ s : ℕ, 1 ≤ s → s ≤ 15 → phenhHighLedger s ≤ 170906186782) :
    JointPHENHSharpBound :=
  joint_phenh_sharp_of_ledger phenh_joint_ledger_reduction
    (phenh_joint_ledger_certificate_of_high hhigh)
-- CHECKPOINT

end ProvenHashes.UMASH
