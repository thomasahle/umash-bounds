import ProvenHashes.UMASHLedgerInteger
import ProvenHashes.UMASHTwistPopcount

/-! Rational square envelopes for the existing conditional twisting weights.
This refines the two-PH counting argument from the GPT-6 Pro handoff of
2026-09-19. Only the 852 established reduction masks are enumerated. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] maskSet

/-- Eleven bounded bisections avoid reduction of the library's unbounded
integer-square-root implementation inside the finite kernel certificates. -/
def twoPHRootSearch (x : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo+1
  | n+1, lo, hi =>
    let mid := (lo+hi)/2
    if mid*mid ≤ x then twoPHRootSearch x n mid hi else twoPHRootSearch x n lo mid

def twoPHRootLowNat (e : ℕ) : ℕ :=
  let h := (maskBitSet 64 e).card
  twoPHRootSearch (min (2^(h+1)) ((maskPatterns e).card*(h+2))*2^20/2^(h+1)) 11 0 1025

def twoPHRootHighNat (e : ℕ) : ℕ :=
  twoPHRootSearch (twistHighWeightNumerator e / 2^44) 11 0 1025

def twoPHRootLow (e : ℕ) : ℚ≥0 := (twoPHRootLowNat e : ℚ≥0) / 1024
def twoPHRootHigh (e : ℕ) : ℚ≥0 := (twoPHRootHighNat e : ℚ≥0) / 1024

theorem two_ph_root_low_certificate : ∀ e ∈ maskSet,
    twistLowPopcountWeight e ≤ (twoPHRootLow e)^2 := by
  rw [maskSet_eq_fastCertificate]
  decide +kernel
-- CHECKPOINT

theorem two_ph_root_high_certificate : ∀ e ∈ maskSet,
    twistHighWeightNumerator e ≤ (twoPHRootHighNat e)^2*2^44 := by
  rw [maskSet_eq_fastCertificate]
  simp only [twoPHRootHighNat, twistHighWeightNumerator, twistHighFactorNumerator_eq_fast]
  decide +kernel
-- CHECKPOINT

theorem two_ph_root_weights (e : ℕ) (he : e ∈ maskSet) :
    twistLowWeight e ≤ (twoPHRootLow e)^2 ∧
    twistHighWeight e ≤ (twoPHRootHigh e)^2 := by
  refine ⟨(twistLowWeight_le_popcount e).trans (two_ph_root_low_certificate e he), ?_⟩
  rw [twistHighWeight_eq_numerator, twoPHRootHigh]
  have hc : (twistHighWeightNumerator e:ℚ≥0) ≤ (twoPHRootHighNat e:ℚ≥0)^2*2^44 := by
    exact_mod_cast two_ph_root_high_certificate e he
  calc
    _ ≤ ((twoPHRootHighNat e:ℚ≥0)^2*2^44)/q :=
      div_le_div_of_nonneg_right hc (zero_le _)
    _ = _ := by norm_num [q]; ring
-- CHECKPOINT

theorem min_le_product_of_square_bounds (a b u v : ℚ≥0)
    (ha : a ≤ u^2) (hb : b ≤ v^2) : min a b ≤ u*v := by
  rcases le_total u v with h | h
  · exact (min_le_left _ _).trans (ha.trans
      (by simpa only [pow_two] using mul_le_mul_of_nonneg_left h (zero_le u)))
  · exact (min_le_right _ _).trans (hb.trans
      (by simpa only [pow_two] using mul_le_mul_of_nonneg_right h (zero_le v)))
-- CHECKPOINT

theorem two_ph_twist_product_weight (u v : ℕ) (hu : u ∈ maskSet) (hv : v ∈ maskSet) :
    min (twistLowWeight u) (twistHighWeight v) ≤ twoPHRootLow u*twoPHRootHigh v :=
  min_le_product_of_square_bounds _ _ _ _
    (two_ph_root_weights u hu).1 (two_ph_root_weights v hv).2
-- CHECKPOINT

def twoPHRootCensus (weight : ℕ → ℕ) (c : ℕ) : ℕ :=
  ∑ r ∈ Finset.range 4, (maskSet.filter (fun u => u%4 = r)).card *
    ∑ v ∈ maskSet.filter (fun v => v%8 = c ^^^ (2*r)), weight v

theorem two_ph_root_total_certificate :
    (∑ e ∈ maskSet, twoPHRootLowNat e) ≤ 47*1024 ∧
    (∑ e ∈ maskSet, twoPHRootHighNat e) ≤ 38*1024 := by
  rw [maskSet_eq_fastCertificate]
  simp only [twoPHRootHighNat, twistHighWeightNumerator, twistHighFactorNumerator_eq_fast]
  decide +kernel
-- CHECKPOINT

theorem two_ph_root_census_certificate : ∀ c : Fin 8,
    twoPHRootCensus twoPHRootLowNat c.val ≤ 7500*1024 ∧
    twoPHRootCensus twoPHRootHighNat c.val ≤ 5700*1024 := by
  simp only [twoPHRootCensus, maskSet_eq_fastCertificate, twoPHRootHighNat,
    twistHighWeightNumerator, twistHighFactorNumerator_eq_fast]
  decide +kernel
-- CHECKPOINT

end ProvenHashes.UMASH
