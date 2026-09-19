import ProvenHashes.UMASHExcludedZeroRoot
import ProvenHashes.UMASHFingerprintMessage

/-! Primary endpoint root and rounding estimates for the argument from the GPT-6 Pro handoff of 2026-09-19, Section 7. -/
namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] uniformProb wordFintype rootRate

theorem probability_mixture_add {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (E : A × B → Prop) (bad : A → Prop)
    (r bound : ℚ≥0) (hb : uniformProb bad ≤ bound)
    (hs : ∀ a, ¬bad a → uniformProb (fun b => E (a,b)) ≤ r) :
    uniformProb E ≤ bound+r := by
  have hm := probability_mixture E bad (min 1 r) bound (min_le_left _ _) hb
    (fun a ha => le_min (probability_le_one _) (hs a ha))
  apply hm.trans
  apply add_le_add_left
  exact (mul_le_mul_of_nonneg_right (tsub_le_self : (1:ℚ≥0)-bound ≤ 1)
    (show (0:ℚ≥0) ≤ min 1 r by positivity)).trans (by simpa only [one_mul] using min_le_right (1:ℚ≥0) r)
-- CHECKPOINT

theorem long_comparison_slice_excluded_zero (L : ℕ) (k : OHKey) (seed : Word) (x y : Message)
    (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L)
    (hxl : 8 < x.length) (hyl : 8 < y.length)
    (hne : comparisonPolynomial k seed x ≠ comparisonPolynomial k seed y) :
    uniformProb (fun f : PolyKey => hashWith k f.val.val seed x = hashWith k f.val.val seed y) ≤
      ((2*((L+31)/32)-1:ℕ):ℚ≥0)/(p-2:ℕ) := by
  let P := comparisonPolynomial k seed x-comparisonPolynomial k seed y
  have hd : P.natDegree ≤ 2*((L+31)/32) :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le
      (comparisonPolynomial_degree L k seed x hx) (comparisonPolynomial_degree L k seed y hy))
  have hz : P.coeff 0 = 0 := long_mode_difference_constant_zero false k seed x y hxl hyl
  apply (probability_mono ?_).trans
    ((polynomial_key_root_probability_zero_constant P (sub_ne_zero.mpr hne) hz).trans
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le_sub_right hd 1)) (by positivity)))
  intro f hf
  simp only [P,Polynomial.eval_sub,sub_eq_zero,comparisonPolynomial_eval]
  exact congrArg (fun a => ((unfinalize a).toNat:Field)) hf
-- CHECKPOINT

theorem primary_bucket_positive (L : ℕ) (hL : 1 ≤ L) : 1 ≤ (L+511)/512 := by omega
-- CHECKPOINT

theorem primary_earlier_rate_le_published (L : ℕ) (hL : 1 ≤ L) :
    ((256:ℚ≥0)/q+((2*((L+31)/32)-1:ℕ):ℚ≥0)/(p-2:ℕ))/
      (((q-561:ℕ):ℚ≥0)/q) ≤ ((L+511)/512:ℕ)/(2:ℚ≥0)^55 := by
  have hJ : (1:ℚ) ≤ ((L+511)/512:ℕ) := by exact_mod_cast primary_bucket_positive L hL
  have hn : 2*((L+31)/32)-1+1 ≤ 32*((L+511)/512) := by omega
  have hnQ : (((2*((L+31)/32)-1:ℕ):ℚ))+1 ≤ 32*(((L+511)/512:ℕ):ℚ) := by exact_mod_cast hn
  apply NNRat.coe_le_coe.mp
  simp only [NNRat.coe_div,NNRat.coe_add,NNRat.coe_natCast,NNRat.coe_pow]
  norm_num [q,p]
  nlinarith only [hJ,hnQ]
-- CHECKPOINT

theorem primary_other_rate_le_published (L : ℕ) (hL : 1 ≤ L) :
    ((82:ℚ≥0)/q+rootRate L)/(((q-561:ℕ):ℚ≥0)/q) ≤
      ((L+511)/512:ℕ)/(2:ℚ≥0)^55 := by
  have hJ : (1:ℚ) ≤ ((L+511)/512:ℕ) := by exact_mod_cast primary_bucket_positive L hL
  have hn : 2*((L+31)/32) ≤ 32*((L+511)/512) := by omega
  have hnQ : (2:ℚ)*(((L+31)/32:ℕ):ℚ) ≤ 32*(((L+511)/512:ℕ):ℚ) := by exact_mod_cast hn
  have hr := NNRat.coe_le_coe.mpr (show rootRate L ≤ 2*(((L+31)/32:ℕ):ℚ≥0)/(p-2:ℕ) from
    by rw [rootRate]; exact min_le_right _ _)
  apply NNRat.coe_le_coe.mp
  norm_num [q,p] at hr ⊢
  nlinarith only [hJ,hnQ,hr]
-- CHECKPOINT

theorem primary_last_rate_le_published (L : ℕ) (hL : 1 ≤ L) :
    ((503:ℚ≥0)/q)/(((q-561:ℕ):ℚ≥0)/q) ≤ ((L+511)/512:ℕ)/(2:ℚ≥0)^55 := by
  have hJ : (1:ℚ≥0) ≤ ((L+511)/512:ℕ) := by exact_mod_cast primary_bucket_positive L hL
  exact (show ((503:ℚ≥0)/q)/(((q-561:ℕ):ℚ≥0)/q) ≤ (1:ℚ≥0)/2^55 by
    apply NNRat.coe_le_coe.mp; norm_num [q]).trans (div_le_div_of_nonneg_right hJ (by positivity))
-- CHECKPOINT

end ProvenHashes.UMASH
