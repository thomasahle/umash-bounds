import ProvenHashes.UMASHLedgerInteger

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] maskSet phenhENHMask phenhPHMask

/-- A popcount-only bound for every high ENH target factor. -/
theorem high_target_ceiling_certificate : ∀ h : Fin 65,
    min ((276:ℚ≥0)*2^(64-h.val)) (16*(2^((h.val+1)/2)+1)) ≤ 134217744 := by
  decide +kernel
-- CHECKPOINT

theorem highTargetK_uniform_le (e : ℕ) : highTargetK e ≤ 134217744 := by
  exact (min_le_right _ _).trans
    (high_target_ceiling_certificate ⟨(maskBitSet 64 e).card, by
      have := mask_bit_set_card_le 64 e
      omega⟩)
-- CHECKPOINT

/-- Integer certificate for the total exact high twisting weight. -/
theorem twist_high_weight_numerator_sum_certificate :
    (∑ v ∈ maskSet, twistHighWeightNumerator v) ≤ 18*q := by
  rw [maskSet_eq_fastCertificate]
  simp only [twistHighWeightNumerator, twistHighFactorNumerator_eq_fast]
  decide +kernel
-- CHECKPOINT

theorem twist_high_weight_sum_certificate :
    (∑ v ∈ maskSet, twistHighWeight v) ≤ 18 := by
  simp only [twistHighWeight_eq_numerator]
  rw [← Finset.sum_div, ← Nat.cast_sum]
  apply (div_le_iff₀ (show (0:ℚ≥0) < q by norm_num [q])).mpr
  exact_mod_cast twist_high_weight_numerator_sum_certificate
-- CHECKPOINT

set_option maxHeartbeats 2000000

/-- A uniform high-ledger ceiling, sufficient for the original 87-bit
OpenPHENH obligation. The separate 90-bit target remains sharper. -/
theorem phenh_high_ledger_open_bound (s : ℕ) :
    phenhHighLedger s ≤ 2058363321984 := by
  have hsum (T : Finset ℕ) (b : ℕ → ℕ → Bool) (g : ℕ → ℕ → ℚ≥0) (w : ℕ → ℚ≥0)
      (hg : ∀ u v, g u v ≤ 134217744) (hw : (∑ v ∈ T, w v) ≤ 18) :
      (∑ u ∈ T, ∑ v ∈ T, if b u v then g u v*w v else 0) ≤
        T.card*134217744*18 := by
    calc
      _ ≤ ∑ _u ∈ T, (134217744:ℚ≥0)*18 := by
        apply Finset.sum_le_sum
        intro u _
        calc
          _ ≤ ∑ v ∈ T, (134217744:ℚ≥0)*w v := by
            apply Finset.sum_le_sum
            intro v _
            split
            · exact mul_le_mul_of_nonneg_right (hg u v) (by positivity)
            · positivity
          _ = (134217744:ℚ≥0) * ∑ v ∈ T, w v := (Finset.mul_sum ..).symm
          _ ≤ (134217744:ℚ≥0)*18 := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hb := hsum maskSet (fun u v => decide ((phenhPHMask s u v).toNat < 2^63))
    (fun u v => highTargetK (phenhENHMask s u v)) twistHighWeight
    (fun _ _ => highTargetK_uniform_le _) twist_high_weight_sum_certificate
  norm_num only [maskSet_card, Nat.cast_ofNat] at hb
  simpa only [phenhHighLedger, decide_eq_true_eq] using hb
-- CHECKPOINT

/-- A closed joint bound for all positive ENH valuations. This does not
claim the still sharper PROOF2 constant 170906186782. -/
theorem joint_phenh_open_bound (seed : Word) (x y : Block)
    (hx : x.Valid) (hy : y.Valid) (hc : sameCount x y)
    (hsum : dataChecksum x = dataChecksum y)
    (hp : phDiffCount x y = 1) (he : enhChanges x y = 2)
    (hr : 1 ≤ enhValuation x y) (hr' : enhValuation x y ≤ 63) :
    uniformProb (jointEvent seed x y) ≤ (2058363321984:ℚ≥0)/q^2 := by
  obtain ⟨s, hs1, hs15, hb⟩ :=
    phenh_joint_ledger_reduction seed x y hx hy hc hsum hp he hr hr'
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs with hv
  · exact (phenh_low_ledger_certificate _ s hr (by omega) hs1 hs15).trans (by norm_num)
  · exact phenh_high_ledger_open_bound s
-- CHECKPOINT

/-- The exact original OpenPHENH proposition is closed unconditionally.
Its 87-bit threshold is weaker than the additional sharp 90-bit target. -/
theorem open_phenh_sharp : OpenPHENH := by
  intro seed x y hx hy hc hsum hp he hr
  exact (joint_phenh_open_bound seed x y hx hy hc hsum hp he (by omega) (by omega)).trans_lt
    (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
