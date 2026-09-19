import ProvenHashes.UMASHPatterns

namespace ProvenHashes.UMASH

set_option maxHeartbeats 2000000

/-- Cancellation by an odd signed coefficient, proved one binary digit at a time. -/
theorem odd_cancel_two_pow (d : ℤ) (hd : d % 2 = 1) (n : ℕ) (t : ℤ)
    (h : (2 : ℤ)^n ∣ d*t) : (2 : ℤ)^n ∣ t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have h2 : (2 : ℤ) ∣ d*t := (dvd_pow_self 2 (by omega : n+1 ≠ 0)).trans h
    have ht : (2 : ℤ) ∣ t := by
      rw [Int.dvd_iff_emod_eq_zero] at h2 ⊢
      simpa only [Int.mul_emod, hd, one_mul, Int.emod_emod] using h2
    obtain ⟨u, rfl⟩ := ht
    have hu : (2 : ℤ)^n ∣ d*u := by
      apply Int.dvd_of_mul_dvd_mul_left (by norm_num : (2 : ℤ) ≠ 0)
      convert h using 1 <;> ring
    obtain ⟨v, hv⟩ := ih u hu
    refine ⟨v, ?_⟩
    rw [hv, pow_succ]
    ring
-- CHECKPOINT

/-- Multiplication followed by a fixed AND and XOR preserves every low-bit prefix. -/
theorem product_mask_prefix (A m c x y j : ℕ)
    (h : x % 2^j = y % 2^j) :
    (((A*x) &&& m) ^^^ c) % 2^j = (((A*y) &&& m) ^^^ c) % 2^j := by
  rw [Nat.xor_mod_two_pow, Nat.xor_mod_two_pow,
    Nat.and_mod_two_pow, Nat.and_mod_two_pow]
  congr 2
  exact Nat.ModEq.mul_left A h
-- CHECKPOINT

/-- The triangular congruence has at most one word solution.  At each step the
odd coefficient determines the next bit, because the varying correction is even. -/
theorem triangular_lift_unique (w : ℕ) (d Q c : ℤ) (hd : d % 2 = 1)
    (z : ℕ → ℕ)
    (hz : ∀ x y j, x % 2^j = y % 2^j → z x % 2^j = z y % 2^j)
    (x y : ℕ) (hx : x < 2^w) (hy : y < 2^w)
    (he : Int.ModEq ((2 : ℤ)^w)
      (d*x+c+2*Q*z x) (d*y+c+2*Q*z y)) : x = y := by
  have hstep : ∀ j, j ≤ w → Int.ModEq ((2 : ℤ)^j) (x : ℤ) (y : ℤ) := by
    intro j
    induction j with
    | zero => intro _; simp [Int.ModEq]
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hn : x % 2^j = y % 2^j := by
        exact Int.natCast_modEq_iff.mp (by exact_mod_cast hi)
      have hzi : Int.ModEq ((2 : ℤ)^j) (z x : ℤ) (z y : ℤ) := by
        exact_mod_cast (Int.natCast_modEq_iff.mpr (hz x y j hn))
      have hz2 : (2 : ℤ)^(j+1) ∣ 2*Q*((z y : ℤ)-z x) := by
        obtain ⟨a, ha⟩ := hzi.dvd
        refine ⟨Q*a, ?_⟩
        rw [ha, pow_succ]
        ring
      have hm : (2 : ℤ)^(j+1) ∣ (2 : ℤ)^w := pow_dvd_pow 2 hj
      have hh := (he.of_dvd hm).dvd
      have hdt : (2 : ℤ)^(j+1) ∣ d*((y : ℤ)-x) := by
        convert dvd_sub hh hz2 using 1 <;> ring
      exact Int.modEq_iff_dvd.mpr (odd_cancel_two_pow d hd (j+1) _ hdt)
  have heq : x % 2^w = y % 2^w := by
    exact Int.natCast_modEq_iff.mp (by exact_mod_cast hstep w le_rfl)
  simpa only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using heq
-- CHECKPOINT

/-- Lemma 4.3's necessary congruence is injective even with an arbitrary common
high mask: its sign pattern is a function of the low product bits. -/
theorem enh_lift_congruence_unique (w A m M t : ℕ) (d Q c : ℤ)
    (hd : d % 2 = 1) (x y : ℕ) (hx : x < 2^w) (hy : y < 2^w)
    (he : Int.ModEq ((2 : ℤ)^w)
      (d*x+c+2*Q*(((A*x &&& m) ^^^ (M &&& m) ^^^ t : ℕ) : ℤ))
      (d*y+c+2*Q*(((A*y &&& m) ^^^ (M &&& m) ^^^ t : ℕ) : ℤ))) : x = y := by
  apply triangular_lift_unique w d Q c hd
    (fun b => (A*b &&& m) ^^^ (M &&& m) ^^^ t) ?_ x y hx hy he
  intro a b j h
  simpa only [Nat.xor_assoc] using product_mask_prefix A m ((M &&& m) ^^^ t) a b j h
-- CHECKPOINT

end ProvenHashes.UMASH
