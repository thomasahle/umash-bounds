import ProvenHashes.UMASHRound3Obligations

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Each dyadic interval contributes at most one to the harmonic sum.
The zero term is zero, so this includes precisely the positive words. -/
theorem dyadic_reciprocal_sum (n : ℕ) :
    (∑ a ∈ Finset.range (2^n), (1:ℚ)/(a:ℚ)) ≤ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : (0:ℚ) < (2^n:ℕ) := by positivity
    have ht : (∑ a ∈ Finset.range (2^n), (1:ℚ)/((2^n+a:ℕ):ℚ)) ≤ 1 := by
      calc
        _ ≤ ∑ _a ∈ Finset.range (2^n), (1:ℚ)/(2^n:ℕ) := by
          apply Finset.sum_le_sum
          intro a _
          apply one_div_le_one_div_of_le hp
          exact_mod_cast Nat.le_add_right (2^n) a
        _ = 1 := by simp [ne_of_gt hp]
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    push_cast at ht ⊢
    linarith
-- CHECKPOINT

/-- A wrapped translation permutes every word in a finite sum. -/
theorem sum_range_wrapped_add (Q δ : ℕ) (hQ : 0 < Q) (hδ : δ < Q)
    (f : ℕ → ℚ) :
    (∑ a ∈ Finset.range Q, f ((a+δ)%Q)) = ∑ a ∈ Finset.range Q, f a := by
  apply Finset.sum_bij (fun a _ => (a+δ)%Q)
  · intro a _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hQ)
  · intro a ha b hb he
    have hm : Nat.ModEq Q (a+δ) (b+δ) := he
    have hc := hm.add_right_cancel' δ
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using hc
  · intro b hb
    have hb := Finset.mem_range.mp hb
    by_cases hd : δ ≤ b
    · refine ⟨b-δ, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Nat.sub_add_cancel hd, Nat.mod_eq_of_lt hb]
    · refine ⟨b+Q-δ, Finset.mem_range.mpr (by omega), ?_⟩
      rw [Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  · intro a _
    rfl
-- CHECKPOINT

/-- The elementary reciprocal inequality, with the two zero cases included. -/
theorem reciprocal_sum_pair_bound (a b : ℕ) :
    (1:ℚ)/(a+b:ℕ) ≤ (1/(a:ℚ)+1/(b:ℚ))/4 +
      (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b; norm_num
    · have hb1 : (1:ℚ) ≤ b := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hb
      have hi : (1:ℚ)/b ≤ 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0:ℚ) < 1) hb1
      simp only [Nat.zero_add, Nat.cast_zero, div_zero, zero_add, if_pos rfl, if_neg hb,
        add_zero, ite_true]
      linarith [show (0:ℚ) ≤ 1/(b:ℚ) by positivity]
  · by_cases hb : b = 0
    · subst b
      have ha1 : (1:ℚ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha
      have hi : (1:ℚ)/a ≤ 1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0:ℚ) < 1) ha1
      simp only [Nat.add_zero, Nat.cast_zero, div_zero, add_zero, if_neg ha, if_pos rfl, ite_true]
      linarith [show (0:ℚ) ≤ 1/(a:ℚ) by positivity]
    · have hap : (0:ℚ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
      have hbp : (0:ℚ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
      simp only [if_neg ha, if_neg hb, add_zero, Nat.cast_add]
      field_simp
      nlinarith [sq_nonneg ((a:ℚ)-b)]
-- CHECKPOINT

/-- The wrapped product-sum slopes have reciprocal sum at most n/2+2.
This accounts for both zero operands without omitting them. -/
theorem wrapped_reciprocal_sum (n δ : ℕ) (hδ : δ < 2^n) :
    (∑ a ∈ Finset.range (2^n), (1:ℚ)/(a+(a+δ)%2^n:ℕ)) ≤ (n:ℚ)/2+2 := by
  let f : ℕ → ℚ := fun a => (1/(a:ℚ))/4 + if a = 0 then 1 else 0
  have hf : (∑ a ∈ Finset.range (2^n), f a) ≤ (n:ℚ)/4+1 := by
    simp only [f, Finset.sum_add_distrib, ← Finset.sum_div]
    have hz : (∑ a ∈ Finset.range (2^n), (if a = 0 then (1:ℚ) else 0)) = 1 := by
      simp [show 0 < 2^n by positivity]
    rw [hz]
    exact add_le_add_right (div_le_div_of_nonneg_right (dyadic_reciprocal_sum n)
      (by norm_num)) _
  calc
    _ ≤ ∑ a ∈ Finset.range (2^n), (f a+f ((a+δ)%2^n)) := by
      apply Finset.sum_le_sum
      intro a _
      have h := reciprocal_sum_pair_bound a ((a+δ)%2^n)
      dsimp only [f]
      linarith
    _ = 2*(∑ a ∈ Finset.range (2^n), f a) := by
      rw [Finset.sum_add_distrib, sum_range_wrapped_add (2^n) δ (by positivity) hδ f]
      ring
    _ ≤ _ := by linarith
-- CHECKPOINT

end ProvenHashes.UMASH
