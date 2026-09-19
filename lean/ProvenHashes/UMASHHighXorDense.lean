import ProvenHashes.UMASHHighSumCount
import ProvenHashes.UMASHLiftingClasses

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

def highCommonPattern (n δ ε tag tag' : ℕ) (ab : ℕ × ℕ) : ℕ :=
  ((ab.1*ab.2/2^n+tag)%2^n) &&&
    (((((ab.1+δ)%2^n)*((ab.2+ε)%2^n))/2^n+tag')%2^n)

/-- The common bits of two words with XOR e vanish on every selected bit
of e, leaving at most 2^(n-h(e)) possible common-bit patterns. -/
theorem high_common_pattern_mem (n δ ε tag tag' e : ℕ) (ab : ℕ × ℕ)
    (he : highTaggedXorEventNat n δ ε tag tag' e ab) :
    highCommonPattern n δ ε tag tag' ab ∈ maskValueTargets n e 0 := by
  let U := (ab.1*ab.2/2^n+tag)%2^n
  let V := ((((ab.1+δ)%2^n)*((ab.2+ε)%2^n))/2^n+tag')%2^n
  change U ^^^ V = e at he
  apply Finset.mem_filter.mpr
  change U &&& V ∈ Finset.range (2^n) ∧ (U &&& V) &&& e = 0
  refine ⟨Finset.mem_range.mpr (Nat.and_le_left.trans_lt (Nat.mod_lt _ (by positivity))), ?_⟩
  rw [← he]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_xor]
  cases U.testBit i <;> cases V.testBit i <;> simp
-- CHECKPOINT

/-- A common-bit pattern fixes the high sum modulo the word size, with
the actual tag additions retained. -/
theorem high_tagged_xor_sum_congruence (n δ ε tag tag' e : ℕ) (ab : ℕ × ℕ)
    (he : highTaggedXorEventNat n δ ε tag tag' e ab) :
    Nat.ModEq (2^n)
      (productHighSum (2^n) ab.1 ((ab.1+δ)%2^n) ε ab.2+(tag+tag'))
      (e+2*highCommonPattern n δ ε tag tag' ab) := by
  let H := ab.1*ab.2/2^n
  let H' := ((ab.1+δ)%2^n)*((ab.2+ε)%2^n)/2^n
  let U := (H+tag)%2^n
  let V := (H'+tag')%2^n
  change U ^^^ V = e at he
  have hs : U+V = e+2*(U &&& V) := by
    have hi := xor_int_expand U V
    rw [he] at hi
    omega
  have hu : Nat.ModEq (2^n) (H+tag) U := (Nat.mod_mod _ _).symm
  have hv : Nat.ModEq (2^n) (H'+tag') V := (Nat.mod_mod _ _).symm
  have hh := hu.add hv
  rw [hs] at hh
  convert hh using 1 <;> dsimp only [productHighSum, highCommonPattern, H, H', U, V] <;> omega
-- CHECKPOINT

/-- A fixed common-bit pattern costs at most (4n+20)Q operand pairs. -/
theorem high_xor_dense_pattern_count (n δ ε tag tag' e z : ℕ)
    (S : Finset (ℕ × ℕ)) (hδ : 0 < δ ∧ δ < 2^n) (hε : ε < 2^n)
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, highTaggedXorEventNat n δ ε tag tag' e ab)
    (hpat : ∀ ab ∈ S, highCommonPattern n δ ε tag tag' ab = z) :
    S.card ≤ (4*n+20)*2^n := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst S; simp
  · obtain ⟨ab₀, hab₀⟩ := hS
    have hc := wrapped_high_sum_count n δ ε
      (productHighSum (2^n) ab₀.1 ((ab₀.1+δ)%2^n) ε ab₀.2%2^n) S hδ hε hbox
      (by
        intro ab hab
        have he₁ := high_tagged_xor_sum_congruence n δ ε tag tag' e ab (hevent ab hab)
        have he₀ := high_tagged_xor_sum_congruence n δ ε tag tag' e ab₀ (hevent ab₀ hab₀)
        rw [hpat ab hab] at he₁
        rw [hpat ab₀ hab₀] at he₀
        exact (he₁.trans he₀.symm).add_right_cancel' (tag+tag'))
    exact_mod_cast hc
-- CHECKPOINT

/-- PROOF2's dense high-XOR count, uniform in the word width and tags.
Only the first increment must be nonzero. -/
theorem high_xor_dense_count (n δ ε tag tag' e : ℕ) (S : Finset (ℕ × ℕ))
    (hδ : 0 < δ ∧ δ < 2^n) (hε : ε < 2^n)
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, highTaggedXorEventNat n δ ε tag tag' e ab) :
    S.card ≤ (4*n+20)*2^(n-(maskBitSet n e).card)*2^n := by
  let G (z : ℕ) := S.filter (fun ab => highCommonPattern n δ ε tag tag' ab = z)
  have hlabel : ∀ ab ∈ S,
      highCommonPattern n δ ε tag tag' ab ∈ maskValueTargets n e 0 :=
    fun ab hab => high_common_pattern_mem n δ ε tag tag' e ab (hevent ab hab)
  have hcard : S.card = ∑ z ∈ maskValueTargets n e 0, (G z).card :=
    Finset.card_eq_sum_card_fiberwise hlabel
  have hg (z : ℕ) : (G z).card ≤ (4*n+20)*2^n :=
    high_xor_dense_pattern_count n δ ε tag tag' e z (G z) hδ hε
      (fun ab hab => hbox ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => hevent ab (Finset.mem_filter.mp hab).1)
      (fun ab hab => (Finset.mem_filter.mp hab).2)
  calc
    _ = ∑ z ∈ maskValueTargets n e 0, (G z).card := hcard
    _ ≤ ∑ _z ∈ maskValueTargets n e 0, (4*n+20)*2^n := Finset.sum_le_sum (fun z _ => hg z)
    _ = (maskValueTargets n e 0).card*((4*n+20)*2^n) := by simp
    _ ≤ 2^(n-(maskBitSet n e).card)*((4*n+20)*2^n) :=
      Nat.mul_le_mul_right _ (mask_value_targets_card_le n e 0)
    _ = _ := by ring
-- CHECKPOINT

/-- Exact finite-uniform probability form of the dense high-XOR count. -/
theorem high_xor_dense_probability (n δ ε tag tag' e : ℕ)
    (hδ : 0 < δ ∧ δ < 2^n) (hε : ε < 2^n) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      highTaggedXorEventNat n δ ε tag tag' e (ab.1.val, ab.2.val)) ≤
      (4*n+20:ℕ)*(2:ℚ≥0)^(n-(maskBitSet n e).card)/(2:ℚ≥0)^n := by
  have hc := fin_pair_probability_of_nat_count (2^n)
    ((4*n+20)*2^(n-(maskBitSet n e).card)*2^n)
    (highTaggedXorEventNat n δ ε tag tag' e)
    (fun S hb he => high_xor_dense_count n δ ε tag tag' e S hδ hε hb he)
  calc
    _ ≤ ((4*n+20:ℕ)*(2:ℚ≥0)^(n-(maskBitSet n e).card)*(2:ℚ≥0)^n)/((2:ℚ≥0)^n)^2 := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    _ = _ := by field_simp
-- CHECKPOINT

/-- The coefficient 276 for literal 64-bit operands and arbitrary tags. -/
theorem high_xor_dense_probability_word (δ ε tag tag' e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : ε < q) :
    uniformProb (fun ab : Word × Word =>
      highTaggedXorEventNat 64 δ ε tag tag' e (ab.1.toNat, ab.2.toNat)) ≤
      (276:ℚ≥0)*2^(64-(maskBitSet 64 e).card)/q := by
  let equiv : (Fin (2^64) × Fin (2^64)) ≃ (Word × Word) :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  exact high_xor_dense_probability 64 δ ε tag tag' e hδ hε
-- CHECKPOINT

/-- The previously recorded first analytic obligation is closed. -/
theorem high_enh_dense_bound : HighENHDenseBound := by
  intro δ ε tag tag' e hδ₀ hδ hε₀ hε he
  exact high_xor_dense_probability_word δ ε tag tag' e ⟨hδ₀,hδ⟩ hε
-- CHECKPOINT

end ProvenHashes.UMASH
