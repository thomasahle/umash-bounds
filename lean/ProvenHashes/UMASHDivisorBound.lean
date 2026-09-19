import ProvenHashes.UMASHENHCount

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-- The six exact finite maxima in PROOF2 Lemma 9.1, in integer form. -/
theorem small_prime_divisor_certificate : ∀ a : Fin 128,
    2*(a.val+1)^4 ≤ 81*2^a.val ∧
    27*(a.val+1)^4 ≤ 256*3^a.val ∧
    25*(a.val+1)^4 ≤ 81*5^a.val ∧
    7*(a.val+1)^4 ≤ 16*7^a.val ∧
    11*(a.val+1)^4 ≤ 16*11^a.val ∧
    13*(a.val+1)^4 ≤ 16*13^a.val := by
  decide +kernel
-- CHECKPOINT

def divisorPrimeFactor (p : ℕ) : ℕ :=
  if p = 2 then 42 else if p = 3 then 10 else if p = 5 then 4 else
  if p = 7 then 3 else if p = 11 then 2 else if p = 13 then 2 else 1

theorem divisorPrimeFactor_ge_one (p : ℕ) : 1 ≤ divisorPrimeFactor p := by
  unfold divisorPrimeFactor
  split_ifs <;> omega
-- CHECKPOINT

/-- Integer ceilings of the exact six factors suffice for the stated 2^36 bound. -/
theorem prime_exponent_divisor_bound (p a : ℕ) (hp : p.Prime) (ha : a < 128) :
    (a+1)^4 ≤ divisorPrimeFactor p * p^a := by
  by_cases h17 : 17 ≤ p
  · have hs : a+1 ≤ 2^a := Nat.lt_two_pow_self
    calc
      _ ≤ (2^a)^4 := Nat.pow_le_pow_left hs 4
      _ = 16^a := by rw [← pow_mul, Nat.mul_comm a 4, pow_mul]; norm_num
      _ ≤ p^a := Nat.pow_le_pow_left (by omega : 16 ≤ p) a
      _ ≤ _ := Nat.le_mul_of_pos_left _ (divisorPrimeFactor_ge_one p)
  · have hc := small_prime_divisor_certificate ⟨a,ha⟩
    dsimp only at hc
    have hlt : p < 17 := by omega
    interval_cases p <;> norm_num [Nat.prime_def_lt] at hp
    all_goals norm_num [divisorPrimeFactor] <;> omega
-- CHECKPOINT

theorem factorization_exponent_lt_128 (n p : ℕ) (hn : n ≠ 0) (hn128 : n < 2^128)
    (hp : p.Prime) : n.factorization p < 128 := by
  by_contra h
  have hd : p^(n.factorization p) ∣ n := by
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn, hp.factorization_pow]
    exact Finsupp.single_le_iff.mpr le_rfl
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have hpow : 2^128 ≤ p^(n.factorization p) := by
    exact (Nat.pow_le_pow_left hp.two_le 128).trans
      (Nat.le_of_dvd (pow_pos hp.pos _) (pow_dvd_pow p (by omega)))
  omega
-- CHECKPOINT

/-- This bound is uniform over all finite subsets of primes, not a list of
experimentally encountered factorizations. -/
theorem divisorPrimeFactor_product_le (s : Finset ℕ) :
    (∏ p ∈ s, divisorPrimeFactor p) ≤ 20160 := by
  let T : Finset ℕ := {2,3,5,7,11,13}
  have hsub : s ⊆ s ∪ T := Finset.subset_union_left
  calc
    _ ≤ ∏ p ∈ s ∪ T, divisorPrimeFactor p :=
      Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p _ _ => divisorPrimeFactor_ge_one p)
    _ = ∏ p ∈ T, divisorPrimeFactor p := by
      symm
      apply Finset.prod_subset Finset.subset_union_right
      intro p _ hp
      have hpn : p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 ∧ p ≠ 11 ∧ p ≠ 13 := by
        simpa only [T, Finset.mem_insert, Finset.mem_singleton, not_or] using hp
      simp only [divisorPrimeFactor, hpn.1, hpn.2.1, hpn.2.2.1,
        hpn.2.2.2.1, hpn.2.2.2.2.1, hpn.2.2.2.2.2, ↓reduceIte]
    _ = 20160 := by norm_num [T, divisorPrimeFactor]
-- CHECKPOINT

/-- PROOF2 Lemma 9.1: every positive 128-bit integer has fewer than 2^36 divisors. -/
theorem divisors_card_lt_two_pow36 (n : ℕ) (hn : 0 < n) (hn128 : n < 2^128) :
    n.divisors.card < 2^36 := by
  have hprod : n.divisors.card^4 ≤ 20160*n := by
    rw [Nat.card_divisors hn.ne', ← Finset.prod_pow]
    calc
      _ ≤ ∏ p ∈ n.primeFactors, divisorPrimeFactor p * p^(n.factorization p) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro p hp
        exact prime_exponent_divisor_bound p (n.factorization p)
          (Nat.prime_of_mem_primeFactors hp)
          (factorization_exponent_lt_128 n p hn.ne' hn128 (Nat.prime_of_mem_primeFactors hp))
      _ = (∏ p ∈ n.primeFactors, divisorPrimeFactor p)*n := by
        rw [Finset.prod_mul_distrib]
        congr 1
        exact Nat.factorization_prod_pow_eq_self hn.ne'
      _ ≤ 20160*n := Nat.mul_le_mul_right n (divisorPrimeFactor_product_le _)
  by_contra h
  have hlo : (2^36)^4 ≤ n.divisors.card^4 := Nat.pow_le_pow_left (by omega) 4
  have hhi : 20160*n < 20160*2^128 := Nat.mul_lt_mul_of_pos_left hn128 (by decide)
  norm_num at hlo hhi
  omega
-- CHECKPOINT

end ProvenHashes.UMASH
