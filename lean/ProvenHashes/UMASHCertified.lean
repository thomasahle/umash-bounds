import ProvenHashes.UMASHShortLongIdentity
import ProvenHashes.UMASHJointClosure

namespace ProvenHashes.UMASH
attribute [local irreducible] uniformProb wordFintype

/-- Corrected all-pairs envelope for the actual 64-bit hash with distinct OH keys. -/
theorem certified_all_pairs64 : CertifiedAllPairs64 :=
  certified64_of_iid_long iid_long_primary_identity_bound
-- CHECKPOINT

theorem corrected_linear64 : CorrectedLinear64 :=
  correctedLinear64_of_certified certified_all_pairs64
-- CHECKPOINT

theorem certified_all_pairs128 : CertifiedAllPairs128 :=
  certifiedAllPairs128_of_64 certified_all_pairs64
-- CHECKPOINT

theorem corrected_linear128 : CorrectedLinear128 :=
  correctedLinear128_of_64 corrected_linear64
-- CHECKPOINT

/-- The same certified envelope also holds under IID sampling. -/
theorem certified_all_pairs64_iid : CertifiedAllPairs64IID := by
  intro L seed x y _hL hx hy hxy
  by_cases hshort : x.length ≤ 8 ∧ y.length ≤ 8
  · have hprob : uniformProb (fun k : OHKey × PolyKey =>
        hashWith k.1 k.2.val.val seed x = hashWith k.1 k.2.val.val seed y) ≤ (1:ℚ≥0)/q := by
      simp only [hashWith, hshort.1, hshort.2, ↓reduceIte]
      rw [Classic.uniformProb_ignore_right (B := PolyKey)
        (fun k : OHKey => shortHash k seed x false = shortHash k seed y false)]
      exact short_collision_iid seed x y hshort.1 hshort.2 hxy
    exact hprob.trans ((show (1:ℚ≥0)/q ≤ (1:ℚ≥0)/(q-561:ℕ) from
      by apply NNRat.coe_le_coe.mp; norm_num [q]).trans (short_bound_le_certifiedEnvelope L))
  · have hlong : 8 < x.length ∨ 8 < y.length := by omega
    have hL : L ≠ 1 := by intro he; subst L; simp only [mul_one] at hx hy; omega
    have hcomp : 1-weakA = weakComplement :=
      tsub_eq_of_eq_add (weakA_add_complement.symm.trans (add_comm _ _))
    rw [certifiedEnvelope, if_neg hL, ← hcomp]
    apply probability_mixture _
      (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y)
      (rootRate L) weakA (min_le_left _ _)
      ((iid_long_primary_identity_bound seed x y hxy hlong).trans
        (by apply NNRat.coe_le_coe.mp; norm_num [q, weakA]))
    intro k hk
    exact comparison_slice_bound L k seed x y hx hy hk
-- CHECKPOINT

end ProvenHashes.UMASH
