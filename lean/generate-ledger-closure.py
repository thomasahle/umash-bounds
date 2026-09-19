"""Assemble the fifteen checked high ledgers into the sharp block theorem."""
from pathlib import Path

imports = '\n'.join(f'import ProvenHashes.UMASHHighCertificate{s}' for s in range(1, 16))
lemmas = ', '.join(f'phenh_high_numerator_{s}' for s in range(1, 16))
Path('Round7PHENHSharp.stage.lean').write_text(imports + '''
import ProvenHashes.UMASHLedgerIntegerAssembly

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] phenhHighLedgerNumerator

/-- All fifteen high ledgers, each obtained by adding kernel-checked row blocks. -/
theorem phenh_high_integer_certificate : ∀ s : Fin 15,
    phenhHighLedgerNumerator (s.val+1) ≤ 170906186782*q := by
  intro s
  fin_cases s <;> norm_num [''' + lemmas + ''', q]
-- CHECKPOINT

theorem phenh_high_ledger_certificate (s : ℕ) (hs1 : 1 ≤ s) (hs15 : s ≤ 15) :
    phenhHighLedger s ≤ 170906186782 := by
  apply (phenh_high_ledger_bound_iff s 170906186782).mpr
  have h := phenh_high_integer_certificate ⟨s-1, by omega⟩
  simpa only [show s-1+1 = s by omega] using h
-- CHECKPOINT

/-- The complete 60-case PROOF2 ledger certificate has no remaining premise. -/
theorem phenh_joint_ledger_certificate : PHENHJointLedgerCertificate :=
  phenh_joint_ledger_certificate_of_high phenh_high_ledger_certificate
-- CHECKPOINT

/-- PROOF2's sharp IID bound on the literal two-compressor block event. -/
theorem joint_phenh_sharp : JointPHENHSharpBound :=
  joint_phenh_sharp_of_high_integer_certificate phenh_high_integer_certificate
-- CHECKPOINT

theorem joint_phenh_iid_lt90 (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hsum : dataChecksum x = dataChecksum y)
    (hp : phDiffCount x y = 1) (he : enhChanges x y = 2)
    (hr : 1 ≤ enhValuation x y) (hr' : enhValuation x y ≤ 63) :
    uniformProb (jointEvent seed x y) < (1:ℚ≥0)/2^90 :=
  (joint_phenh_sharp seed x y hx hy hc hsum hp he hr hr').trans_lt
    phenh_sharp_arithmetic.1
-- CHECKPOINT

theorem joint_phenh_distinct_lt90 (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hsum : dataChecksum x = dataChecksum y)
    (hp : phDiffCount x y = 1) (he : enhChanges x y = 2)
    (hr : 1 ≤ enhValuation x y) (hr' : enhValuation x y ≤ 63) :
    uniformProb (fun k : DistinctOHKey => jointEvent seed x y k.val) < (1:ℚ≥0)/2^90 :=
  phenh_distinct_of_sharp_joint joint_phenh_sharp seed x y hx hy hc hsum hp he hr hr'
-- CHECKPOINT

''')

path = Path('Round7PHENHSharp.stage.lean')
with path.open('a') as output:
    output.write('''
/-- The exact maximum of the fifteen high ledgers is attained at s=2. -/
theorem phenh_high_ledger_maximum (s : Fin 15) :
    phenhHighLedger (s.val+1) ≤ phenhHighLedger 2 := by
  rw [phenhHighLedger_eq_numerator, phenhHighLedger_eq_numerator,
    phenh_high_numerator_2]
  fin_cases s <;> apply NNRat.coe_le_coe.mp <;>
    norm_num [''' + lemmas + ''', q]
-- CHECKPOINT

/-- All three low-ledger rows lie below the attained high-ledger maximum. -/
theorem phenh_low_ledger_below_high_maximum (r s : ℕ)
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hs1 : 1 ≤ s) (hs15 : s ≤ 15) :
    phenhLowLedger r s ≤ phenhHighLedger 2 := by
  have hW1 : (∑ v ∈ valuationMasks 1, twistLowWeight v) ≤ 10 :=
    (Finset.sum_le_sum (fun v _ => twistLowWeight_le_popcount v)).trans
      twist_low_popcount_sum_certificate.1
  have hW2 : (∑ v ∈ valuationMasks 2, twistLowWeight v) ≤ 4 :=
    (Finset.sum_le_sum (fun v _ => twistLowWeight_le_popcount v)).trans
      twist_low_popcount_sum_certificate.2
  interval_cases r
  · have hC : ∀ e, lowTargetK 1 e ≤ 34078720 :=
      fun e => lowTargetK_small_valuation_le (0:Fin 2) e
    apply (phenh_low_ledger_uniform_bound 1 s 34078720 10 hC hW1).trans
    rw [phenhHighLedger_eq_numerator, phenh_high_numerator_2]
    apply NNRat.coe_le_coe.mp
    norm_num [valuationMasks_card_table.2.1, q]
  · have hC : ∀ e, lowTargetK 2 e ≤ 67108864 :=
      fun e => lowTargetK_small_valuation_le (1:Fin 2) e
    apply (phenh_low_ledger_uniform_bound 2 s 67108864 4 hC hW2).trans
    rw [phenhHighLedger_eq_numerator, phenh_high_numerator_2]
    apply NNRat.coe_le_coe.mp
    norm_num [valuationMasks_card_table.2.2.1, q]
  · have h := phenh_low_ledger_r3_certificate ⟨s-1, by omega⟩
    have he : s-1+1 = s := by omega
    simp only [he] at h
    apply h.trans
    rw [phenhHighLedger_eq_numerator, phenh_high_numerator_2]
    apply NNRat.coe_le_coe.mp
    norm_num [q]
-- CHECKPOINT

def phenhLedgerCase (row : Fin 4) (s : Fin 15) : ℚ≥0 :=
  if row.val < 3 then phenhLowLedger (row.val+1) (s.val+1)
  else phenhHighLedger (s.val+1)

attribute [local irreducible] phenhHighLedger phenhLowLedger

/-- The maximum of all sixty cases, including an explicit attaining case. -/
theorem phenh_sixty_case_maximum :
    (∀ row : Fin 4, ∀ s : Fin 15, phenhLedgerCase row s ≤ phenhHighLedger 2) ∧
      phenhLedgerCase 3 1 = phenhHighLedger 2 := by
  constructor
  · intro row s
    unfold phenhLedgerCase
    split_ifs with h
    · exact phenh_low_ledger_below_high_maximum _ _ (by omega) (by omega)
        (by omega) (by have := s.isLt; omega)
    · exact phenh_high_ledger_maximum s
  · rfl
-- CHECKPOINT

end ProvenHashes.UMASH
''')
