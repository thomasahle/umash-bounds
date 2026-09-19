import ProvenHashes.UMASHIndependentRoots

/-! Averaging the two independent polynomial-root bounds. The use of coarse
marginals for the published fingerprint endpoint follows the argument from
the GPT-6 Pro handoff of 2026-09-19, Sections 3 and 9; the stronger constants
are retained separately. No compressor bound is assumed as an axiom. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb

theorem probability_scaled_indicator {K : Type*} [Fintype K] (E : K → Prop)
    [DecidablePred E] (c : ℚ≥0) :
    (∑ k, if E k then c else 0)/(Fintype.card K : ℚ≥0) = uniformProb E*c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  unfold uniformProb
  have hf : @Finset.filter K E inferInstance Finset.univ =
      @Finset.filter K E (fun k => Classical.propDecidable (E k)) Finset.univ := by
    ext k
    simp
  rw [hf]
  ring
-- CHECKPOINT

theorem probability_joint_mixture {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (E : A × B → Prop) (bad0 bad1 : A → Prop) (r : ℚ≥0)
    (hs : ∀ a, uniformProb (fun b => E (a,b)) ≤
      (if bad0 a then 1 else r)*(if bad1 a then 1 else r)) :
    uniformProb E ≤ r^2+r*(uniformProb bad0+uniformProb bad1)+
      uniformProb (fun a => bad0 a ∧ bad1 a) := by
  classical
  have hcard : (Fintype.card A : ℚ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpoint (a : A) : (if bad0 a then 1 else r)*(if bad1 a then 1 else r) ≤
      r^2+(if bad0 a then r else 0)+(if bad1 a then r else 0)+
        (if bad0 a ∧ bad1 a then 1 else 0) := by
    apply NNRat.coe_le_coe.mp
    have hr : (0:ℚ) ≤ r := r.property
    by_cases h0 : bad0 a <;> by_cases h1 : bad1 a <;>
      norm_num [h0, h1] <;> nlinarith only [hr, sq_nonneg (r:ℚ)]
  rw [probability_prod]
  calc
    _ ≤ (∑ a, (r^2+(if bad0 a then r else 0)+(if bad1 a then r else 0)+
        (if bad0 a ∧ bad1 a then 1 else 0)))/(Fintype.card A : ℚ≥0) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => (hs a).trans (hpoint a)))
        (by positivity)
    _ = _ := by
      simp only [Finset.sum_add_distrib, add_div]
      rw [probability_scaled_indicator bad0 r, probability_scaled_indicator bad1 r,
        probability_scaled_indicator (fun a => bad0 a ∧ bad1 a) 1]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_div_cancel_left₀ _ hcard, mul_one]
      ring
-- CHECKPOINT

theorem averaged_independent_polynomial_roots {K : Type*} [Fintype K] [Nonempty K]
    (P0 P1 : K → Polynomial Field) (d : ℕ)
    (h0 : ∀ k, (P0 k).natDegree ≤ d) (h1 : ∀ k, (P1 k).natDegree ≤ d) :
    uniformProb (fun k : K × (PolyKey × PolyKey) =>
      (P0 k.1).eval (k.2.1.val.val : Field) = 0 ∧
        (P1 k.1).eval (k.2.2.val.val : Field) = 0) ≤
      (min 1 ((d:ℚ≥0)/(p-2:ℕ)))^2+
        min 1 ((d:ℚ≥0)/(p-2:ℕ)) *
          (uniformProb (fun k => P0 k = 0)+uniformProb (fun k => P1 k = 0))+
        uniformProb (fun k => P0 k = 0 ∧ P1 k = 0) := by
  apply probability_joint_mixture
  intro k
  have h := independent_polynomial_root_product (P0 k) (P1 k) d (h0 k) (h1 k)
  by_cases hz0 : P0 k = 0 <;> by_cases hz1 : P1 k = 0 <;>
    simpa only [hz0, hz1, ite_true, ite_false] using h
-- CHECKPOINT

end ProvenHashes.UMASH
