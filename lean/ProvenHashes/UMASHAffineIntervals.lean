import ProvenHashes.UMASHReciprocalSums

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Integer inputs to a positive-slope affine map are spaced by its slope. -/
theorem nat_affine_interval_count (S : Finset ℕ) (s c l ell : ℚ)
    (hs : 0 < s) (hell : 0 ≤ ell)
    (hinterval : ∀ b ∈ S, l ≤ s*b+c ∧ s*b+c < l+ell) :
    (S.card:ℚ) ≤ ell/s+1 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst S
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · let x := S.min' hS
    let y := S.max' hS
    have hx : x ∈ S := S.min'_mem hS
    have hy : y ∈ S := S.max'_mem hS
    have hxy : x ≤ y := S.min'_le y hy
    have hc : S.card ≤ (Finset.Icc x y).card := by
      apply Finset.card_le_card
      intro b hb
      exact Finset.mem_Icc.mpr ⟨S.min'_le b hb, S.le_max' b hb⟩
    rw [Nat.card_Icc] at hc
    have hc' : S.card+x ≤ y+1 := by omega
    have hcQ : (S.card:ℚ)+(x:ℚ) ≤ (y:ℚ)+1 := by exact_mod_cast hc'
    have hi : s*((y:ℚ)-x) ≤ ell := by
      have hl := (hinterval x hx).1
      have hu := (hinterval y hy).2
      linarith
    have hw : (y:ℚ)-x ≤ ell/s := (le_div_iff₀ hs).mpr (by nlinarith [hi])
    linarith
-- CHECKPOINT

/-- A prescribed sum of product high words confines the full product sum
to an interval of length 2Q, even when their low words are different. -/
theorem product_high_sum_interval (Q A B A' B' t : ℕ) (hQ : 0 < Q)
    (ht : A*B/Q+A'*B'/Q = t) :
    (Q:ℚ)*t ≤ (A:ℚ)*B+(A':ℚ)*B' ∧
      (A:ℚ)*B+(A':ℚ)*B' < (Q:ℚ)*t+2*Q := by
  have h₁ : (A:ℚ)*B = (A*B%Q:ℕ)+(Q:ℚ)*(A*B/Q:ℕ) := by
    exact_mod_cast (Nat.mod_add_div (A*B) Q).symm
  have h₂ : (A':ℚ)*B' = (A'*B'%Q:ℕ)+(Q:ℚ)*(A'*B'/Q:ℕ) := by
    exact_mod_cast (Nat.mod_add_div (A'*B') Q).symm
  have hm₁ : (A*B%Q:ℕ) < (Q:ℚ) := by exact_mod_cast Nat.mod_lt (A*B) hQ
  have hm₂ : (A'*B'%Q:ℕ) < (Q:ℚ) := by exact_mod_cast Nat.mod_lt (A'*B') hQ
  have htQ : (A*B/Q:ℕ)+(A'*B'/Q:ℕ) = (t:ℚ) := by exact_mod_cast ht
  have hz₁ : (0:ℚ) ≤ (A*B%Q:ℕ) := by positivity
  have hz₂ : (0:ℚ) ≤ (A'*B'%Q:ℕ) := by positivity
  constructor <;> nlinarith
-- CHECKPOINT

/-- One operand-wrap branch and one integer high sum give an affine count. -/
theorem wrapped_high_sum_branch_count (Q A A' ε k t : ℕ) (S : Finset ℕ)
    (hQ : 0 < Q) (hs : 0 < A+A')
    (hwrap : ∀ b ∈ S, (b+ε)/Q = k)
    (hsum : ∀ b ∈ S, A*b/Q+A'*((b+ε)%Q)/Q = t) :
    (S.card:ℚ) ≤ 2*Q/(A+A':ℕ)+1 := by
  rw [Nat.cast_add]
  apply nat_affine_interval_count S ((A:ℚ)+A')
    ((A':ℚ)*(ε-(Q:ℚ)*k)) ((Q:ℚ)*t) (2*Q)
    (by exact_mod_cast hs) (by positivity)
  intro b hb
  have hi := product_high_sum_interval Q A b A' ((b+ε)%Q) t hQ (hsum b hb)
  have hb' : (((b+ε)%Q:ℕ):ℚ) = (b:ℚ)+ε-(Q:ℚ)*k := by
    have hw := Nat.mod_add_div (b+ε) Q
    rw [hwrap b hb] at hw
    have hwQ : (((b+ε)%Q:ℕ):ℚ)+(Q:ℚ)*k = (b:ℚ)+ε := by exact_mod_cast hw
    linarith
  rw [hb'] at hi
  convert hi using 1 <;> ring
-- CHECKPOINT

end ProvenHashes.UMASH
