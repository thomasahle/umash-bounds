import ProvenHashes.UMASHMaskRefinements

namespace ProvenHashes.UMASH
open scoped BigOperators
attribute [local irreducible] maskSet

theorem valuationMasks_eq_zero (r : ℕ) (hr : 4 ≤ r) : valuationMasks r = {0} := by
  ext d
  constructor
  · intro hd
    obtain ⟨hd, hm⟩ := Finset.mem_filter.mp hd
    have hd16 : 16 ∣ d := (pow_dvd_pow 2 hr).trans (Nat.dvd_of_mod_eq_zero hm)
    have h : d ∈ maskSet.filter (fun d => d%16 = 0) :=
      Finset.mem_filter.mpr ⟨hd, Nat.mod_eq_zero_of_dvd hd16⟩
    rw [maskSet_mod_sixteen] at h
    exact h
  · intro hd
    have hd0 := Finset.mem_singleton.mp hd
    subst d
    have h : 0 ∈ maskSet.filter (fun d => d%16 = 0) := by
      rw [maskSet_mod_sixteen]
      exact Finset.mem_singleton_self _
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1, Nat.zero_mod _⟩
-- CHECKPOINT

theorem patternWeight_ge_four (r : ℕ) (hr : 4 ≤ r) : patternWeight r = 1 := by
  rw [patternWeight, valuationMasks_eq_zero r hr, Finset.sum_singleton]
  decide +kernel
-- CHECKPOINT

theorem valuationMasks_card_ge_four (r : ℕ) (hr : 4 ≤ r) : (valuationMasks r).card = 1 := by
  rw [valuationMasks_eq_zero r hr, Finset.card_singleton]
-- CHECKPOINT

end ProvenHashes.UMASH
