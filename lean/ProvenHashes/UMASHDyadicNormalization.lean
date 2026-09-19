import ProvenHashes.UMASHLowCoordinates

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

/-- Two coefficients which are not both zero modulo 2^n have a common
power-of-two factor with a primitive quotient, including zero coefficients. -/
theorem dyadic_primitive_factor (n : ℕ) (b c : ℤ)
    (hn : ¬((2:ℤ)^n ∣ b ∧ (2:ℤ)^n ∣ c)) :
    ∃ s < n, ∃ b' c' : ℤ,
      b = (2:ℤ)^s*b' ∧ c = (2:ℤ)^s*c' ∧ (b'%2 = 1 ∨ c'%2 = 1) := by
  induction n generalizing b c with
  | zero => simp at hn
  | succ n ih =>
    by_cases ho : b%2 = 1 ∨ c%2 = 1
    · exact ⟨0, by omega, b, c, by simp, by simp, ho⟩
    · have hb : b = 2*(b/2) := by omega
      have hc : c = 2*(c/2) := by omega
      have hn' : ¬((2:ℤ)^n ∣ b/2 ∧ (2:ℤ)^n ∣ c/2) := by
        intro h
        apply hn
        constructor
        · rw [hb, pow_succ, mul_comm ((2:ℤ)^n)]
          exact mul_dvd_mul_left 2 h.1
        · rw [hc, pow_succ, mul_comm ((2:ℤ)^n)]
          exact mul_dvd_mul_left 2 h.2
      obtain ⟨s, hs, b', c', hb', hc', ho'⟩ := ih (b/2) (c/2) hn'
      refine ⟨s+1, by omega, b', c', ?_, ?_, ho'⟩
      · calc
          b = 2*(b/2) := hb
          _ = (2:ℤ)^(s+1)*b' := by rw [hb', pow_succ]; ring
      · calc
          c = 2*(c/2) := hc
          _ = (2:ℤ)^(s+1)*c' := by rw [hc', pow_succ]; ring
-- CHECKPOINT

/-- Removing zero low mask bits preserves the number of selected positions. -/
theorem mask_bit_set_div_pow_card (n s e : ℕ) (hs : s ≤ n) (he : 2^s ∣ e) :
    (maskBitSet (n-s) (e/2^s)).card = (maskBitSet n e).card := by
  apply Finset.card_bij (fun i _ => (⟨i.val+s, by omega⟩ : Fin n))
  · intro i hi
    have hi := (Finset.mem_filter.mp hi).2
    simp only [maskBitSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (Nat.testBit_div_two_pow e i.val).symm.trans hi
  · intro i _ j _ hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    dsimp only at hv
    omega
  · intro j hj
    have hjbit : e.testBit j.val = true := (Finset.mem_filter.mp hj).2
    have hsj : s ≤ j.val := by
      by_contra h
      have hz := congrArg (fun x : ℕ => x.testBit j.val) (Nat.mod_eq_zero_of_dvd he)
      simp only [Nat.testBit_mod_two_pow, Nat.testBit_zero, hjbit, Bool.and_true] at hz
      have : j.val < s := by omega
      simp [this] at hz
    refine ⟨⟨j.val-s, by omega⟩, ?_, ?_⟩
    · simp only [maskBitSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Nat.testBit_div_two_pow, Nat.sub_add_cancel hsj, hjbit]
    · apply Fin.ext
      exact Nat.sub_add_cancel hsj
-- CHECKPOINT

/-- A primitive quadratic count at a smaller modulus, with all high input
digits retained. Each reduced input has exactly 2^s possible lifts. -/
theorem quadratic_small_set_lift_count (n s h : ℕ) (hs : s ≤ n) (hh : h ≤ n-s)
    (b c d : ℤ) (T : Finset ℤ) (hodd : b%2 = 1 ∨ c%2 = 1)
    (hT : T.card ≤ 2^(n-s-h)) (S : Finset ℕ)
    (hbox : ∀ A ∈ S, A < 2^n)
    (hevent : ∀ A ∈ S, quadraticValue b c d A % (2:ℤ)^(n-s) ∈ T) :
    S.card ≤ 4*2^(n-h/2) := by
  let m := n-s
  let U := Finset.univ.filter (fun x : Fin (2^m) =>
    quadraticValue b c d x.val % (2:ℤ)^m ∈ T)
  let f (A : ℕ) : ℕ × Fin (2^m) :=
    (A/2^m, ⟨A%2^m, Nat.mod_lt _ (by positivity)⟩)
  have hp : 2^n = 2^m*2^s := by
    rw [← pow_add, show m+s = n from Nat.sub_add_cancel hs]
  have hc : S.card ≤ 2^s*quadraticSetCount m b c d T := by
    calc
      _ ≤ ((Finset.range (2^s)) ×ˢ U).card := by
        apply Finset.card_le_card_of_injOn f
        · intro A hA
          apply Finset.mem_product.mpr
          constructor
          · apply Finset.mem_range.mpr
            apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^m)).mpr
            simpa only [hp, Nat.mul_comm] using hbox A hA
          · apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            have ha : Int.ModEq ((2:ℤ)^m) (A:ℤ) ((A%2^m:ℕ):ℤ) := by
              simpa only [Nat.cast_pow, Nat.cast_ofNat] using
                (Int.natCast_modEq_iff.mpr (Nat.mod_mod A (2^m)).symm)
            have he := ((ha.pow 2).mul_left b |>.add (ha.mul_left c)).add_right d
            change quadraticValue b c d ((A%2^m:ℕ):ℤ) % (2:ℤ)^m ∈ T
            unfold quadraticValue
            rw [← he]
            exact hevent A hA
        · intro A _ B _ hab
          have hh := congrArg Prod.fst hab
          have hl := congrArg (fun u : ℕ × Fin (2^m) => u.2.val) hab
          dsimp only [f] at hh hl
          have hA := Nat.mod_add_div A (2^m)
          have hB := Nat.mod_add_div B (2^m)
          rw [hh, hl] at hA
          exact hA.symm.trans hB
      _ = _ := by rw [Finset.card_product, Finset.card_range]; rfl
  have hsmall := quadratic_small_set_count m h hh b c d T hodd hT
  calc
    S.card ≤ 2^s*quadraticSetCount m b c d T := hc
    _ ≤ 2^s*(4*2^(m-h/2)) := Nat.mul_le_mul_left _ hsmall
    _ = 4*2^(n-h/2) := by
      rw [← mul_assoc, Nat.mul_comm (2^s) 4, mul_assoc, ← pow_add]
      congr 2
      dsimp only [m]
      omega
-- CHECKPOINT

/-- A scaled quadratic with an odd multiplier retains the same selected-bit
bound. Its common zero low bits are removed before applying the primitive
quadratic theorem; multiplication only permutes the reduced target set. -/
theorem scaled_quadratic_mask_count (n s e z a : ℕ) (b c : ℤ)
    (hs : s ≤ n) (he : 2^s ∣ e) (ha : a%2 = 1)
    (hodd : b%2 = 1 ∨ c%2 = 1) (S : Finset ℕ)
    (hbox : ∀ A ∈ S, A < 2^n)
    (hevent : ∀ A ∈ S, ∃ Y : ℕ, Y < 2^n ∧ Y &&& e = z ∧
      Int.ModEq ((2:ℤ)^n) ((a:ℤ)*Y)
        ((2:ℤ)^s*(b*(A:ℤ)^2+c*A))) :
    S.card ≤ 4*2^(n-(maskBitSet n e).card/2) := by
  let m := n-s
  let U := maskValueTargets m (e/2^s) (z/2^s)
  let T : Finset ℤ := U.image (fun y : ℕ => ((a:ℤ)*y) % (2:ℤ)^m)
  have hcard := mask_bit_set_div_pow_card n s e hs he
  have hh : (maskBitSet n e).card ≤ n-s := by
    rw [← hcard]
    exact mask_bit_set_card_le _ _
  have hT : T.card ≤ 2^(n-s-(maskBitSet n e).card) := by
    calc
      T.card ≤ U.card := Finset.card_image_le
      _ ≤ _ := by
        simpa only [U, m, hcard] using mask_value_targets_card_le m (e/2^s) (z/2^s)
  apply quadratic_small_set_lift_count n s (maskBitSet n e).card hs hh b c 0 T hodd hT S hbox
  intro A hA
  obtain ⟨Y, hY, hz, hcong⟩ := hevent A hA
  have hdiv : (2:ℤ)^s ∣ (a:ℤ)*Y := by
    apply Int.modEq_zero_iff_dvd.mp
    exact (hcong.of_dvd (pow_dvd_pow (2:ℤ) hs)).trans (dvd_mul_right _ _).modEq_zero_int
  have hdivN : 2^s ∣ a*Y := by exact_mod_cast hdiv
  have hac : Nat.Coprime (2^s) a :=
    ((Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ha)).pow_right s).symm
  have hYd : 2^s ∣ Y := hac.dvd_of_dvd_mul_left hdivN
  have hYeq : Y = 2^s*(Y/2^s) := (Nat.mul_div_cancel' hYd).symm
  have hp : 2^n = 2^s*2^m := by
    rw [← pow_add, Nat.add_sub_of_le hs]
  have hpI : (2:ℤ)^n = (2:ℤ)^s*(2:ℤ)^m := by exact_mod_cast hp
  have hYeI : (Y:ℤ) = (2:ℤ)^s*(Y/2^s:ℕ) := by exact_mod_cast hYeq
  have hcancel : Int.ModEq ((2:ℤ)^m) ((a:ℤ)*(Y/2^s:ℕ))
      (b*(A:ℤ)^2+c*A) := by
    apply Int.ModEq.mul_left_cancel' (by positivity : (2:ℤ)^s ≠ 0)
    convert hcong using 1 <;> simp only [hpI, hYeI] <;> ring
  have hmem : Y/2^s ∈ U := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^s)).mpr
      simpa only [hp, Nat.mul_comm] using hY
    · rw [← Nat.and_div_two_pow, hz]
  unfold quadraticValue
  rw [add_zero, ← hcancel]
  exact Finset.mem_image.mpr ⟨Y/2^s, hmem, rfl⟩
-- CHECKPOINT

end ProvenHashes.UMASH
