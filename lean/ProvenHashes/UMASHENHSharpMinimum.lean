import ProvenHashes.UMASHENH3125

namespace ProvenHashes.UMASH
attribute [local irreducible] uniformProb wordFintype

theorem enh_low_equal_probability_scale (r δ ε tag tag' M : ℕ)
    (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hodd : (δ/2^r)%2 = 1) :
    uniformProb (enhLowEqualEvent δ ε tag tag' M) ≤ ((2^r:ℕ):ℚ≥0)/q := by
  apply (probability_mono ?_).trans (low_additive_target_le r δ ε hr hδ hε hodd 0)
  intro ab he
  have hh := congrArg (fun a : ℕ => (a : ZMod q)) he.1
  simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add] at hh
  calc
    _ = ((ab.1.toNat:ZMod q)+δ)*((ab.2.toNat:ZMod q)+ε)-
        (ab.1.toNat:ZMod q)*ab.2.toNat := by ring
    _ = 0 := sub_eq_zero.mpr hh.symm
-- CHECKPOINT

/-- The sharper minimum in PROOF3 Theorem 5.4, before taking the maximum over r. -/
theorem enh_high_valuation_minimum (r δ ε tag tag' ML MH : ℕ)
    (h4 : 4 ≤ r) (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hδq : δ < q) (hεq : ε < q) (hML : ML < q) (hMH : MH < q) :
    uniformProb (enhProjectedEvent δ ε tag tag' ML MH) ≤
      min (((2^r:ℕ):ℚ≥0)/q) (((2*(liftingClasses r).card-1:ℕ):ℚ≥0)/q) := by
  have hd16 : 16 ∣ δ := (pow_dvd_pow 2 h4).trans hδ
  have he16 : 16 ∣ ε := (pow_dvd_pow 2 h4).trans hε
  have hm := probability_mono (enh_projected_implies_low_equal δ ε tag tag' ML MH hd16 he16 hML)
  exact le_min (hm.trans (enh_low_equal_probability_scale r δ ε tag tag' MH hr hδ hε hodd))
    (hm.trans (enh_grouped_class_probability r δ ε tag tag' MH h4 hr hδ hε hodd hδq hεq hMH))
-- CHECKPOINT

end ProvenHashes.UMASH
