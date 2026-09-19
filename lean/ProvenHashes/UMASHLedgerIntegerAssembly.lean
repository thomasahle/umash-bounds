import ProvenHashes.UMASHLedgerInteger

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] phenhHighLedgerNumerator

/-- The remaining high-ledger inequalities are equivalent to natural-number
inequalities, with no rounding or probabilistic premise. -/
theorem phenh_high_ledger_bound_iff (s C : ℕ) :
    phenhHighLedger s ≤ (C:ℚ≥0) ↔ phenhHighLedgerNumerator s ≤ C*q := by
  rw [phenhHighLedger_eq_numerator,
    div_le_iff₀ (show (0:ℚ≥0) < q by norm_num [q])]
  constructor <;> intro h <;> exact_mod_cast h
-- CHECKPOINT

/-- The sharp PROOF2 theorem now reduces to fifteen purely integer sums. -/
theorem joint_phenh_sharp_of_high_integer_certificate
    (hhigh : ∀ s : Fin 15,
      phenhHighLedgerNumerator (s.val+1) ≤ 170906186782*q) : JointPHENHSharpBound := by
  apply joint_phenh_sharp_of_high_ledger
  intro s hs1 hs15
  apply (phenh_high_ledger_bound_iff s 170906186782).mpr
  have h := hhigh ⟨s-1, by omega⟩
  have hs : s-1+1 = s := by omega
  simpa only [hs] using h
-- CHECKPOINT

end ProvenHashes.UMASH
