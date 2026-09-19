import ProvenHashes.UMASHENHPointMass

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype Finset.filter Finset.product

/-- On one fixed quotient interval, reduction modulo a sufficiently long period
is injective. This avoids estimates of rounded interval endpoints. -/
theorem mul_div_residue_injective (Q a S h : ℕ) (hQ : 0 < Q) (hS : Q ≤ a*S)
    (b c : ℕ) (hb : a*b/Q = h) (hc : a*c/Q = h) (he : b%S = c%S) : b = c := by
  have hlt (b c : ℕ) (hb : a*b/Q = h) (hc : a*c/Q = h)
      (he : b%S = c%S) (hlt : b < c) : False := by
    have hstep := (show Nat.ModEq S b c from he).add_le_of_lt hlt
    have hmul := Nat.mul_le_mul_left a hstep
    have hbr := Nat.mod_add_div (a*b) Q
    have hcr := Nat.mod_add_div (a*c) Q
    rw [hb] at hbr
    rw [hc] at hcr
    have hbm := Nat.mod_lt (a*b) hQ
    have hcm := Nat.mod_lt (a*c) hQ
    rw [Nat.mul_add] at hmul
    omega
  rcases lt_trichotomy b c with hbc | hbc | hbc
  · exact False.elim (hlt b c hb hc he hbc)
  · exact hbc
  · exact False.elim (hlt c b hc hb he.symm hbc)
-- CHECKPOINT

theorem nat_product_slice_count (Q a S h : ℕ) (hQ : 0 < Q) (hS : Q ≤ a*S) :
    (Finset.univ.filter (fun b : Fin Q => a*b.val/Q = h)).card ≤ S := by
  classical
  have hSp : 0 < S := by
    by_contra hn
    have hz : S = 0 := by omega
    rw [hz, Nat.mul_zero] at hS
    omega
  calc
    _ ≤ (Finset.range S).card := by
      apply Finset.card_le_card_of_injOn (fun b : Fin Q => b.val%S)
      · intro b _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hSp)
      · intro b hb c hc he
        apply Fin.ext
        exact mul_div_residue_injective Q a S h hQ hS b.val c.val
          (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2 he
    _ = S := Finset.card_range S
-- CHECKPOINT

theorem dyadic_sum_bound (f : ℕ → ℕ) (C n : ℕ)
    (h : ∀ j, j < n → ∑ a ∈ Finset.Ico (2^j) (2^(j+1)), f a ≤ C) :
    ∑ a ∈ Finset.Ico 1 (2^n), f a ≤ n*C := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : (2:ℕ)^n ≤ 2^(n+1) := by
      rw [pow_succ]
      omega
    rw [← Finset.sum_Ico_consecutive f (Nat.one_le_two_pow) hpow]
    calc
      _ ≤ n*C+C := Nat.add_le_add (ih (fun j hj => h j (by omega))) (h n (by omega))
      _ = (n+1)*C := by ring
-- CHECKPOINT

/-- At most one full 2^n budget per dyadic interval, and one for A=0. -/
theorem high_product_count (n h : ℕ) :
    (Finset.univ.filter (fun ab : Fin (2^n) × Fin (2^n) =>
      ab.1.val*ab.2.val/2^n = h)).card ≤ (n+1)*2^n := by
  classical
  let f (a : ℕ) := (Finset.univ.filter (fun b : Fin (2^n) => a*b.val/2^n = h)).card
  have hQ : 0 < (2:ℕ)^n := by positivity
  have hblock (j : ℕ) (hj : j < n) :
      ∑ a ∈ Finset.Ico (2^j) (2^(j+1)), f a ≤ 2^n := by
    have hp : (2:ℕ)^j * 2^(n-j) = 2^n := by
      rw [← pow_add, Nat.add_sub_of_le hj.le]
    calc
      _ ≤ ∑ _a ∈ Finset.Ico (2^j) (2^(j+1)), 2^(n-j) := by
        apply Finset.sum_le_sum
        intro a ha
        apply nat_product_slice_count _ _ _ _ hQ
        rw [← hp]
        exact Nat.mul_le_mul_right _ (Finset.mem_Ico.mp ha).1
      _ = 2^n := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
        have hd : (2:ℕ)^(j+1)-2^j = 2^j := by rw [pow_succ]; omega
        rw [hd]
        exact_mod_cast hp
  have hzero : f 0 ≤ 2^n := by
    exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)
  have hsum : ∑ a ∈ Finset.range (2^n), f a ≤ (n+1)*2^n := by
    rw [← Finset.sum_range_add_sum_Ico f (show 1 ≤ (2:ℕ)^n from Nat.one_le_two_pow)]
    simp only [Finset.sum_range_one]
    calc
      _ ≤ 2^n+n*2^n := Nat.add_le_add hzero (dyadic_sum_bound f (2^n) n hblock)
      _ = _ := by ring
  have hc : (Finset.univ.filter (fun ab : Fin (2^n) × Fin (2^n) =>
        ab.1.val*ab.2.val/2^n = h)).card = ∑ a ∈ Finset.range (2^n), f a := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [f, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  rw [hc]
  exact hsum
-- CHECKPOINT

/-- A slightly stronger dyadic estimate for the high-product point mass. -/
theorem high_product_point_mass_le (h : ℕ) :
    uniformProb (fun ab : Word × Word => ab.1.toNat*ab.2.toNat/q = h) ≤ (65:ℚ≥0)/q := by
  classical
  let e : (Fin q × Fin q) ≃ (Word × Word) :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv e (fun ab : Word × Word => ab.1.toNat*ab.2.toNat/q = h)]
  have hc := high_product_count 64 h
  have he : (fun ab : Fin q × Fin q => (e ab).1.toNat*(e ab).2.toNat/q = h) =
      (fun ab => ab.1.val*ab.2.val/q = h) := rfl
  rw [he]
  unfold uniformProb
  rw [Fintype.card_prod, Fintype.card_fin]
  calc
    _ ≤ ((65*q:ℕ):ℚ≥0)/(q*q:ℕ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Nat.cast_le.mpr
      convert hc using 1 <;> congr 1
      ext ab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, q]
    _ = (65:ℚ≥0)/q := by norm_num [q]
-- CHECKPOINT

/-- Lemma 6.1 for the actual independent operand words. -/
theorem high_product_point_mass : HighProductPointMass := by
  intro h
  exact (high_product_point_mass_le h).trans_lt (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
