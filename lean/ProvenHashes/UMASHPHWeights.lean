import ProvenHashes.UMASHPHSelected

namespace ProvenHashes.UMASH
open Polynomial
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype clmul

/-- Degree j means that the word is in the dyadic interval [2^j,2^(j+1)). -/
theorem bitPolynomial_degree_word_range (d : Word) (hd : d ≠ 0) :
    2^(bitPolynomial d).natDegree ≤ d.toNat ∧
      d.toNat < 2^((bitPolynomial d).natDegree+1) := by
  have hlead := (bitPolynomial_leading d hd).2
  constructor
  · by_contra h
    have hz := Nat.testBit_lt_two_pow (by omega : d.toNat < 2^(bitPolynomial d).natDegree)
    change d.toNat.testBit (bitPolynomial d).natDegree = true at hlead
    rw [hz] at hlead
    contradiction
  · by_contra h
    obtain ⟨i, hi, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow
      (by omega : d.toNat ≥ 2^((bitPolynomial d).natDegree+1))
    have hc : (bitPolynomial d).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [coeff_bitPolynomial] at hc
    change bitCoeff (d.toNat.testBit i) = 0 at hc
    norm_num [hbit, bitCoeff] at hc
-- CHECKPOINT

/-- There are at most 2^j words with prescribed nonzero carryless degree j. -/
theorem word_degree_class_count (j : ℕ) :
    (Finset.univ.filter (fun d : Word => d ≠ 0 ∧ (bitPolynomial d).natDegree = j)).card ≤ 2^j := by
  calc
    _ ≤ (Finset.range (2^j)).card := by
      apply Finset.card_le_card_of_injOn (fun d : Word => d.toNat-2^j)
      · intro d hd
        obtain ⟨hd0, hdj⟩ := (Finset.mem_filter.mp hd).2
        have hr := bitPolynomial_degree_word_range d hd0
        rw [hdj, pow_succ] at hr
        apply Finset.mem_range.mpr
        change d.toNat-2^j < 2^j
        omega
      · intro d hd d' hd' he
        obtain ⟨hd0, hdj⟩ := (Finset.mem_filter.mp hd).2
        obtain ⟨hd0', hdj'⟩ := (Finset.mem_filter.mp hd').2
        have hr := (bitPolynomial_degree_word_range d hd0).1
        have hr' := (bitPolynomial_degree_word_range d' hd0').1
        rw [hdj] at hr
        rw [hdj'] at hr'
        apply BitVec.eq_of_toNat_eq
        dsimp only at he
        omega
    _ = _ := Finset.card_range _
-- CHECKPOINT

/-- There are at most 2^(63-j) words with prescribed finite valuation j. -/
theorem word_valuation_class_count (j : ℕ) (hj : j < 64) :
    (Finset.univ.filter (fun d : Word => d ≠ 0 ∧ (bitPolynomial d).natTrailingDegree = j)).card ≤
      2^(63-j) := by
  have hform (d : Word) (hd : d ≠ 0) (hdj : (bitPolynomial d).natTrailingDegree = j) :
      d.toNat = 2^j*(1+2*(d.toNat/2^(j+1))) := by
    have hd0 : 0 < d.toNat := by
      by_contra h
      apply hd
      apply BitVec.eq_of_toNat_eq
      change d.toNat = 0
      omega
    have hval : padicValNat 2 d.toNat = j := (bitPolynomial_trailing_eq_padic d hd).symm.trans hdj
    have hf := dyadic_increment_padic_factor 64 d.toNat ⟨hd0,d.isLt⟩
    rw [hval] at hf
    have hm := Nat.mod_add_div (d.toNat/2^j) 2
    rw [hf.2.2, Nat.div_div_eq_div_mul, ← pow_succ] at hm
    calc
      d.toNat = 2^j*(d.toNat/2^j) := (Nat.mul_div_cancel' hf.2.1).symm
      _ = _ := by rw [← hm]
  have hp : 2^(63-j)*2^(j+1) = 2^64 := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (Finset.range (2^(63-j))).card := by
      apply Finset.card_le_card_of_injOn (fun d : Word => d.toNat/2^(j+1))
      · intro d _hd
        apply Finset.mem_range.mpr
        apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^(j+1))).mpr
        rw [hp]
        exact d.isLt
      · intro d hd d' hd' he
        obtain ⟨hd0, hdj⟩ := (Finset.mem_filter.mp hd).2
        obtain ⟨hd0', hdj'⟩ := (Finset.mem_filter.mp hd').2
        apply BitVec.eq_of_toNat_eq
        dsimp only at he
        rw [hform d hd0 hdj, hform d' hd0' hdj', he]
    _ = _ := Finset.card_range _
-- CHECKPOINT

/-- Average a conditional bound over a finite partition, keeping one
exceptional first coordinate as its own event. -/
theorem finite_pair_class_probability {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty B] [DecidableEq A] (a₀ : A) (m : ℕ) (E : A × B → Prop)
    (label : A → ℕ) (count : ℕ → ℕ) (rate : ℕ → ℚ≥0)
    (hlabel : ∀ d : A, d ≠ a₀ → label d < m)
    (hcount : ∀ j < m,
      (Finset.univ.filter (fun d : A => d ≠ a₀ ∧ label d = j)).card ≤ count j)
    (hslice : ∀ d : A, d ≠ a₀ → uniformProb (fun k => E (d,k)) ≤ rate (label d)) :
    uniformProb E ≤ (1:ℚ≥0)/(Fintype.card A:ℚ≥0) + ∑ j ∈ Finset.range m, (count j:ℚ≥0)*rate j/(Fintype.card A:ℚ≥0) := by
  classical
  let U : Finset A := Finset.univ.erase a₀
  let f (d : A) := uniformProb (fun k => E (d,k))
  have hu : insert a₀ U = Finset.univ := Finset.insert_erase (Finset.mem_univ _)
  have hsum : (∑ d : A, f d) = f a₀ + ∑ d ∈ U, f d := by
    conv_lhs => rw [← hu]
    rw [Finset.sum_insert (Finset.notMem_erase a₀ Finset.univ)]
  have hmap (d : A) (hd : d ∈ U) : label d ∈ Finset.range m :=
    Finset.mem_range.mpr (hlabel d (Finset.ne_of_mem_erase hd))
  have hnonzero : (∑ d ∈ U, f d) ≤ ∑ j ∈ Finset.range m, (count j:ℚ≥0)*rate j := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap f]
    apply Finset.sum_le_sum
    intro j hj
    have hset : U.filter (fun d => label d = j) =
        Finset.univ.filter (fun d : A => d ≠ a₀ ∧ label d = j) := by
      ext d
      simp [U]
    calc
      _ ≤ ∑ _d ∈ U.filter (fun d => label d = j), rate j := by
        apply Finset.sum_le_sum
        intro d hd
        have hdu := (Finset.mem_filter.mp hd).1
        have hdj := (Finset.mem_filter.mp hd).2
        simpa only [hdj] using hslice d (Finset.ne_of_mem_erase hdu)
      _ = ((U.filter (fun d => label d = j)).card:ℚ≥0)*rate j := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (zero_le _)
        rw [hset]
        exact_mod_cast hcount j (Finset.mem_range.mp hj)
  rw [probability_prod]
  change (∑ d : A, f d)/(Fintype.card A:ℚ≥0) ≤ _
  calc
    _ ≤ (1+∑ j ∈ Finset.range m, (count j:ℚ≥0)*rate j)/(Fintype.card A:ℚ≥0) := by
      apply div_le_div_of_nonneg_right _ (zero_le _)
      rw [hsum]
      exact add_le_add (probability_le_one _) hnonzero
    _ = _ := by rw [add_div, Finset.sum_div]
-- CHECKPOINT

/-- PROOF2 f_H, written without negative powers for exact rational evaluation. -/
def twistHighFactor (e : ℕ) : ℚ≥0 :=
  1/q + ∑ j ∈ Finset.range 64, (2:ℚ≥0)^j*(1/2^(maskBitSet j e).card)/q

/-- PROOF2 f_L; the quotient mask has width 64-j. -/
def twistLowFactor (e : ℕ) : ℚ≥0 :=
  1/q + ∑ j ∈ Finset.range 64,
    (2:ℚ≥0)^(63-j)*(1/2^(maskBitSet (64-j) (e/2^j)).card)/q

/-- Averaging the fixed-degree selected-bit count proves the high checksum
pattern weight, uniformly over every fixed offset and selected pattern. -/
theorem clmul_high_pattern_probability (offset : Word) (e z : ℕ) :
    uniformProb (fun ab : Word × Word =>
      (offset ^^^ (split (clmul ab.1 ab.2)).2).toNat &&& e = z) ≤ twistHighFactor e := by
  let label (d : Word) := (bitPolynomial d).natDegree
  have hh := finite_pair_class_probability (0:Word) 64
    (fun ab => (offset ^^^ (split (clmul ab.1 ab.2)).2).toNat &&& e = z)
    label (fun j => 2^j) (fun j => 1/2^(maskBitSet j e).card)
    (fun d hd => (bitPolynomial_leading d hd).1)
    (fun j _ => word_degree_class_count j)
    (fun d hd => clmul_high_mask_probability d hd offset e z)
  simpa only [twistHighFactor, word_card, Nat.cast_pow, Nat.cast_ofNat] using hh
-- CHECKPOINT

/-- Averaging the fixed-valuation selected-bit count proves the low checksum
pattern weight, uniformly over every fixed offset and selected pattern. -/
theorem clmul_low_pattern_probability (offset : Word) (e z : ℕ) :
    uniformProb (fun ab : Word × Word =>
      (offset ^^^ (split (clmul ab.1 ab.2)).1).toNat &&& e = z) ≤ twistLowFactor e := by
  let label (d : Word) := (bitPolynomial d).natTrailingDegree
  have hh := finite_pair_class_probability (0:Word) 64
    (fun ab => (offset ^^^ (split (clmul ab.1 ab.2)).1).toNat &&& e = z)
    label (fun j => 2^(63-j)) (fun j => 1/2^(maskBitSet (64-j) (e/2^j)).card)
    (fun d hd => (bitPolynomial_trailing d hd).1)
    (fun j hj => word_valuation_class_count j hj)
    (fun d hd => clmul_low_mask_probability d hd offset e z)
  simpa only [twistLowFactor, word_card, Nat.cast_pow, Nat.cast_ofNat] using hh
-- CHECKPOINT

end ProvenHashes.UMASH
