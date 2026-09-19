import ProvenHashes.UMASHENHCount

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
attribute [local irreducible] wordFintype uniformProb Finset.univ Finset.range Finset.filter

theorem int_dvd_eq_zero_of_bounds (n d : ℤ) (hd : n ∣ d)
    (hlo : -n < d) (hhi : d < n) : d = 0 := by
  by_cases h : 0 ≤ d
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h hhi hd
  · have hh := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ -d)
      (by omega : -d < n) (dvd_neg.mpr hd)
    omega
-- CHECKPOINT

/-- The full product-difference residue is injective in B even across its
wrap boundary. This includes A=0 and A'=0. -/
theorem wrapped_product_difference_ne (Q A A' ε B₁ B₂ : ℕ)
    (hQ : 0 < Q) (hA : A < Q) (hA' : A' < Q) (hne : A ≠ A')
    (hε : ε < Q) (h₁ : B₁ < B₂) (h₂ : B₂ < Q) :
    ¬Int.ModEq ((Q:ℤ)^2)
      ((A':ℤ)*((B₁+ε)%Q : ℕ)-(A:ℤ)*B₁)
      ((A':ℤ)*((B₂+ε)%Q : ℕ)-(A:ℤ)*B₂) := by
  intro he
  have hw₁ : (B₁+ε)/Q < 2 := by
    apply (Nat.div_lt_iff_lt_mul hQ).mpr
    omega
  have hw₂ : (B₂+ε)/Q < 2 := by
    apply (Nat.div_lt_iff_lt_mul hQ).mpr
    omega
  have hwm : (B₁+ε)/Q ≤ (B₂+ε)/Q := Nat.div_le_div_right (by omega)
  have wrap_cases (u v : ℕ) (hu : u < 2) (hv : v < 2) (huv : u ≤ v) :
      u = v ∨ (u = 0 ∧ v = 1) := by omega
  have hcases := wrap_cases _ _ hw₁ hw₂ hwm
  have hmod₁ : (((B₁+ε)%Q : ℕ):ℤ) + (Q:ℤ)*((B₁+ε)/Q : ℕ) = B₁+ε := by
    exact_mod_cast Nat.mod_add_div (B₁+ε) Q
  have hmod₂ : (((B₂+ε)%Q : ℕ):ℤ) + (Q:ℤ)*((B₂+ε)/Q : ℕ) = B₂+ε := by
    exact_mod_cast Nat.mod_add_div (B₂+ε) Q
  have hT : 0 < (B₂:ℤ)-B₁ := by omega
  have hTQ : (B₂:ℤ)-B₁ < Q := by omega
  have hQZ : (0:ℤ) < Q := by omega
  have hAZ : (A:ℤ) < Q := by omega
  have hA'Z : (A':ℤ) < Q := by omega
  rcases hcases with hw | ⟨hwz₁,hwz₂⟩
  · have hz : (((B₂+ε)%Q : ℕ):ℤ) - ((B₁+ε)%Q : ℕ) = (B₂:ℤ)-B₁ := by
      rw [hw] at hmod₁
      linarith
    have hd : (Q:ℤ)^2 ∣ ((A':ℤ)-A)*((B₂:ℤ)-B₁) := by
      convert he.dvd using 1 <;> nlinarith [hz]
    have hb : (A:ℤ)*((B₂:ℤ)-B₁) < (Q:ℤ)^2 := by
      have hh := (mul_lt_mul_of_pos_right hAZ hT).trans
        (mul_lt_mul_of_pos_left hTQ hQZ)
      nlinarith
    have hb' : (A':ℤ)*((B₂:ℤ)-B₁) < (Q:ℤ)^2 := by
      have hh := (mul_lt_mul_of_pos_right hA'Z hT).trans
        (mul_lt_mul_of_pos_left hTQ hQZ)
      nlinarith
    have hp : 0 ≤ (A:ℤ)*((B₂:ℤ)-B₁) := mul_nonneg (by positivity) hT.le
    have hp' : 0 ≤ (A':ℤ)*((B₂:ℤ)-B₁) := mul_nonneg (by positivity) hT.le
    have hzero := int_dvd_eq_zero_of_bounds ((Q:ℤ)^2) _ hd (by nlinarith) (by nlinarith)
    have ha : (A':ℤ)-A = 0 := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hT)
    exact hne (by omega)
  · rw [hwz₁] at hmod₁
    rw [hwz₂] at hmod₂
    norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, add_zero, mul_one] at hmod₁ hmod₂
    have hz : (((B₂+ε)%Q : ℕ):ℤ) - ((B₁+ε)%Q : ℕ) = (B₂:ℤ)-B₁-Q := by omega
    let D : ℤ := (A':ℤ)*((B₂:ℤ)-B₁-Q)-(A:ℤ)*((B₂:ℤ)-B₁)
    have hd : (Q:ℤ)^2 ∣ D := by
      convert he.dvd using 1 <;> dsimp only [D] <;> nlinarith [hz]
    have hQT : (0:ℤ) < Q-((B₂:ℤ)-B₁) := by omega
    have hsum : (A':ℤ)*(Q-((B₂:ℤ)-B₁))+(A:ℤ)*((B₂:ℤ)-B₁) < (Q:ℤ)^2 := by
      have ha := mul_lt_mul_of_pos_right hA'Z hQT
      have hb := mul_lt_mul_of_pos_right hAZ hT
      nlinarith
    have hsumpos : 0 < (A':ℤ)*(Q-((B₂:ℤ)-B₁))+(A:ℤ)*((B₂:ℤ)-B₁) := by
      have hp : 0 < A' ∨ 0 < A := by omega
      rcases hp with hp | hp <;> positivity
    have hzero := int_dvd_eq_zero_of_bounds ((Q:ℤ)^2) D hd
      (by dsimp only [D]; nlinarith) (by dsimp only [D]; nlinarith [sq_nonneg (Q:ℤ)])
    dsimp only [D] at hzero
    nlinarith
-- CHECKPOINT

theorem wrapped_product_difference_unique (Q A A' ε B₁ B₂ : ℕ)
    (hQ : 0 < Q) (hA : A < Q) (hA' : A' < Q) (hne : A ≠ A')
    (hε : ε < Q) (h₁ : B₁ < Q) (h₂ : B₂ < Q)
    (he : Int.ModEq ((Q:ℤ)^2)
      ((A':ℤ)*((B₁+ε)%Q : ℕ)-(A:ℤ)*B₁)
      ((A':ℤ)*((B₂+ε)%Q : ℕ)-(A:ℤ)*B₂)) : B₁ = B₂ := by
  rcases lt_trichotomy B₁ B₂ with h | h | h
  · exact (wrapped_product_difference_ne Q A A' ε B₁ B₂ hQ hA hA' hne hε h h₂ he).elim
  · exact h
  · exact (wrapped_product_difference_ne Q A A' ε B₂ B₁ hQ hA hA' hne hε h h₁ he.symm).elim
-- CHECKPOINT

theorem wrapped_add_ne (Q A δ : ℕ) (hA : A < Q) (hδ : δ < Q) (hδ0 : δ ≠ 0) :
    (A+δ)%Q ≠ A := by
  intro h
  have hm : Nat.ModEq Q (A+δ) (A+0) := by
    simpa only [Nat.ModEq, add_zero, Nat.mod_eq_of_lt hA] using h
  have hc := Nat.ModEq.add_left_cancel' A hm
  have hz : δ = 0 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hδ, Nat.zero_mod] using hc
  exact hδ0 hz
-- CHECKPOINT

end ProvenHashes.UMASH
