import ProvenHashes.UMASHLowDistribution

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype maskSet maskPatterns

theorem wrapped_product_mod_two_pow (r A B δ ε : ℕ) (hr : r ≤ 64)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) :
    (A*B%q)%2^r = (((A+δ)%q)*((B+ε)%q)%q)%2^r := by
  have hq : 2^r ∣ q := pow_dvd_pow 2 hr
  have ha : ((A+δ)%q)%2^r = A%2^r := by
    rw [Nat.mod_mod_of_dvd _ hq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hδ]
    simp only [Nat.add_zero, Nat.mod_mod]
  have hb : ((B+ε)%q)%2^r = B%2^r := by
    rw [Nat.mod_mod_of_dvd _ hq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hε]
    simp only [Nat.add_zero, Nat.mod_mod]
  rw [Nat.mod_mod_of_dvd _ hq, Nat.mod_mod_of_dvd _ hq]
  conv_rhs => rw [Nat.mul_mod, ha, hb]
  exact Nat.mul_mod _ _ _
-- CHECKPOINT

def lowPatternTarget (M : ℕ) (dt : Σ _ : ℕ, ℕ) : ZMod q :=
  (dt.1 : ZMod q)-2*(((M &&& dt.1) ^^^ dt.2 : ℕ) : ZMod q)

/-- The common XOR offset and its pattern specify the additive target exactly. -/
theorem low_mask_target (M L L' : ℕ) :
    (L' : ZMod q)-(L : ZMod q) =
      lowPatternTarget M ⟨L ^^^ L', (M ^^^ L) &&& (L ^^^ L')⟩ := by
  let d := L ^^^ L'
  let t := (M ^^^ L) &&& d
  have ht : L &&& d = (M &&& d) ^^^ t := by
    simpa only [Nat.xor_zero, Nat.zero_and, Nat.zero_xor] using
      xor_pattern_recover M 0 L d t (by simp only [Nat.xor_zero, t])
  have hs : (L' : ℤ)-L = (d : ℤ)-2*(((M &&& d) ^^^ t : ℕ) : ℤ) := by
    have h := xor_signed_difference L L'
    change (L : ℤ)-L' = 2*(L &&& d : ℕ)-(d : ℤ) at h
    rw [ht] at h
    omega
  have hc := congrArg (fun z : ℤ => (z : ZMod q)) hs
  simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat,
    lowPatternTarget, d, t] using hc
-- CHECKPOINT

/-- Every low projected collision supplies a certified mask-pattern pair. -/
theorem low_projection_cover (r δ ε M : ℕ) (hr : r ≤ 64)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (hM : M < q) (ab : Word × Word)
    (he : (M ^^^ (ab.1.toNat*ab.2.toNat%q))%p =
      (M ^^^ (((ab.1.toNat+δ)%q)*((ab.2.toNat+ε)%q)%q))%p) :
    ∃ dt ∈ (valuationMasks r).sigma maskPatterns,
      (δ : ZMod q)*(ab.2.toNat : ZMod q)+(ε : ZMod q)*(ab.1.toNat : ZMod q)+
        (δ : ZMod q)*(ε : ZMod q) = lowPatternTarget M dt := by
  let L := ab.1.toNat*ab.2.toNat%q
  let L' := ((ab.1.toNat+δ)%q)*((ab.2.toNat+ε)%q)%q
  let d := L ^^^ L'
  let t := (M ^^^ L) &&& d
  have hL : L < q := Nat.mod_lt _ (by norm_num [q])
  have hL' : L' < q := Nat.mod_lt _ (by norm_num [q])
  have hX : M ^^^ L < q := Nat.xor_lt_two_pow hM hL
  have hY : M ^^^ L' < q := Nat.xor_lt_two_pow hM hL'
  have hm : (M ^^^ L) ^^^ (M ^^^ L') = d := by
    simpa only [Nat.xor_zero] using xor_common_cancel M 0 L L'
  have hd : d ∈ valuationMasks r := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hm]
      exact congruent_xor_mem_maskSet _ _ hX hY he
    · dsimp only [d]
      rw [Nat.xor_mod_two_pow,
        show L%2^r = L'%2^r from wrapped_product_mod_two_pow r _ _ δ ε hr hδ hε,
        Nat.xor_self]
  have ht : t ∈ maskPatterns d := by
    have hh := congruent_pattern _ _ hX hY he
    rwa [hm] at hh
  refine ⟨⟨d,t⟩, Finset.mem_sigma.mpr ⟨hd, ht⟩, ?_⟩
  calc
    _ = (L' : ZMod q)-(L : ZMod q) := by
      dsimp only [L, L']
      simp only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add]
      ring
    _ = _ := low_mask_target M L L'
-- CHECKPOINT

/-- Lemma 4.2: union bound over the certified patterns, retaining their valuation. -/
theorem low_projection_bound : LowProjectionBound := by
  intro r δ ε M hr hδ hε hodd hM
  classical
  let T := (valuationMasks r).sigma maskPatterns
  let E := fun (dt : Σ _ : ℕ, ℕ) (ab : Word × Word) =>
    (δ : ZMod q)*(ab.2.toNat : ZMod q)+(ε : ZMod q)*(ab.1.toNat : ZMod q)+
      (δ : ZMod q)*(ε : ZMod q) = lowPatternTarget M dt
  have hc : T.card = patternWeight r := by
    dsimp only [T]
    rw [Finset.card_sigma]
    rfl
  calc
    _ ≤ uniformProb (fun ab => ∃ dt ∈ T, E dt ab) := by
      apply probability_mono
      exact fun ab he => low_projection_cover r δ ε M hr.le hδ hε hM ab he
    _ ≤ ∑ dt ∈ T, uniformProb (E dt) := probability_union_bound T E
    _ ≤ ∑ _dt ∈ T, ((2^r : ℕ) : ℚ≥0)/q := by
      apply Finset.sum_le_sum
      intro dt _
      exact low_additive_target_le r δ ε hr hδ hε hodd (lowPatternTarget M dt)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_mul]
      ring
-- CHECKPOINT

/-- All valuations, arbitrary tags, and both arbitrary common XOR masks. -/
theorem enh_projected_probability (r δ ε tag tag' ML MH : ℕ)
    (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hεq : ε < q) (hML : ML < q) (hMH : MH < q) :
    uniformProb (enhProjectedEvent δ ε tag tag' ML MH) ≤ (5542:ℚ≥0)/q := by
  by_cases h4 : 4 ≤ r
  · exact enh_high_valuation_probability r δ ε tag tag' ML MH
      h4 hr hδ hε hodd hεq hML hMH
  · have hc : 2^r*patternWeight r ≤ 5542 := by
      have hr4 : r < 4 := by omega
      interval_cases r <;> norm_num [patternWeight_table.1, patternWeight_table.2.1,
        patternWeight_table.2.2.1, patternWeight_table.2.2.2.1]
    exact (probability_mono (fun ab (he : enhProjectedEvent δ ε tag tag' ML MH ab) => he.1)).trans
      ((low_projection_bound r δ ε ML hr hδ hε hodd hML).trans
        (div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity)))
-- CHECKPOINT

end ProvenHashes.UMASH
