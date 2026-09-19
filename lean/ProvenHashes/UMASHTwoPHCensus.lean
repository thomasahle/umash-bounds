import ProvenHashes.UMASHTwoPHWeights

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet twoPHRootLowNat twoPHRootHighNat

theorem two_ph_compatibility_residue (u v c : ℕ) :
    (v ^^^ (2*u))%8 = c ↔ v%8 = c ^^^ (2*(u%4)) := by
  have hm : (2*u)%8 = 2*(u%4) := by omega
  change (v ^^^ (2*u))%2^3 = c ↔ _
  rw [Nat.xor_mod_two_pow, hm]
  constructor <;> intro h
  · have he := congrArg (fun z : ℕ => z ^^^ (2*(u%4))) h
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] using he
  · rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
-- CHECKPOINT

theorem two_ph_compatibility_sum (S : Finset ℕ) (weight : ℕ → ℕ) (c : ℕ) :
    (∑ u ∈ S, ∑ v ∈ S, if (v ^^^ (2*u))%8 = c then weight v else 0) =
    ∑ r ∈ Finset.range 4, (S.filter (fun u => u%4 = r)).card *
      ∑ v ∈ S.filter (fun v => v%8 = c ^^^ (2*r)), weight v := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (show ∀ u ∈ S, u%4 ∈ Finset.range 4 from
      fun u _ => Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))
    (fun u => ∑ v ∈ S, if (v ^^^ (2*u))%8 = c then weight v else 0)]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = ∑ _u ∈ S.filter (fun u => u%4 = r),
        ∑ v ∈ S.filter (fun v => v%8 = c ^^^ (2*r)), weight v := by
      apply Finset.sum_congr rfl
      intro u hu
      have hur := (Finset.mem_filter.mp hu).2
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [two_ph_compatibility_residue, hur]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
-- CHECKPOINT

theorem two_ph_root_census_eq (weight : ℕ → ℕ) (c : ℕ) :
    (∑ u ∈ maskSet, ∑ v ∈ maskSet, if (v ^^^ (2*u))%8 = c then weight v else 0) =
    twoPHRootCensus weight c := two_ph_compatibility_sum maskSet weight c
-- CHECKPOINT

theorem two_ph_root_census_bounds (c : ℕ) :
    (∑ u ∈ maskSet, ∑ v ∈ maskSet,
      if (v ^^^ (2*u))%8 = c then twoPHRootLow v else 0) ≤ (7500:ℚ≥0) ∧
    (∑ u ∈ maskSet, ∑ v ∈ maskSet,
      if (v ^^^ (2*u))%8 = c then twoPHRootHigh v else 0) ≤ (5700:ℚ≥0) := by
  have hsum (weight : ℕ → ℕ) :
      (∑ u ∈ maskSet, ∑ v ∈ maskSet,
        if (v ^^^ (2*u))%8 = c then (weight v:ℚ≥0)/1024 else 0) =
      (twoPHRootCensus weight c:ℚ≥0)/1024 := by
    rw [← two_ph_root_census_eq]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Finset.sum_div, ite_div, zero_div]
  by_cases hc : c < 8
  · obtain ⟨hL,hH⟩ := two_ph_root_census_certificate ⟨c,hc⟩
    constructor
    · rw [show (∑ u ∈ maskSet, ∑ v ∈ maskSet,
        if (v ^^^ (2*u))%8 = c then twoPHRootLow v else 0) =
          (twoPHRootCensus twoPHRootLowNat c:ℚ≥0)/1024 from hsum twoPHRootLowNat]
      apply (div_le_iff₀ (by norm_num : (0:ℚ≥0) < 1024)).mpr
      exact_mod_cast hL
    · rw [show (∑ u ∈ maskSet, ∑ v ∈ maskSet,
        if (v ^^^ (2*u))%8 = c then twoPHRootHigh v else 0) =
          (twoPHRootCensus twoPHRootHighNat c:ℚ≥0)/1024 from hsum twoPHRootHighNat]
      apply (div_le_iff₀ (by norm_num : (0:ℚ≥0) < 1024)).mpr
      exact_mod_cast hH
  · have hne (u v : ℕ) : (v ^^^ (2*u))%8 ≠ c := by
      have hm := Nat.mod_lt (v ^^^ (2*u)) (by decide : 0 < 8)
      omega
    simp only [hne, ↓reduceIte, Finset.sum_const_zero, zero_le, and_self]
-- CHECKPOINT

theorem two_ph_root_total_bounds :
    (∑ e ∈ maskSet, twoPHRootLow e) ≤ (47:ℚ≥0) ∧
    (∑ e ∈ maskSet, twoPHRootHigh e) ≤ (38:ℚ≥0) := by
  obtain ⟨hL,hH⟩ := two_ph_root_total_certificate
  constructor
  · simp only [twoPHRootLow, ← Finset.sum_div, ← Nat.cast_sum]
    apply (div_le_iff₀ (by norm_num : (0:ℚ≥0) < 1024)).mpr
    exact_mod_cast hL
  · simp only [twoPHRootHigh, ← Finset.sum_div, ← Nat.cast_sum]
    apply (div_le_iff₀ (by norm_num : (0:ℚ≥0) < 1024)).mpr
    exact_mod_cast hH
-- CHECKPOINT

end ProvenHashes.UMASH
