import ProvenHashes.UMASHShortProbability

namespace ProvenHashes.UMASH
open scoped BigOperators
attribute [local irreducible] uniformProb

/-- Multiply a primary probability by a uniform conditional bound. -/
theorem probability_and_prod_le {A B : Type*} [Fintype A] [Fintype B]
    (E : A → Prop) (F : A × B → Prop) (c : ℚ≥0)
    (hs : ∀ a, uniformProb (fun b => F (a,b)) ≤ c) :
    uniformProb (fun ab => E ab.1 ∧ F ab) ≤ uniformProb E*c := by
  classical
  rw [probability_prod]
  calc
    _ ≤ (∑ a, if E a then c else 0)/(Fintype.card A : ℚ≥0) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro a _
      by_cases h : E a
      · simpa only [h, true_and, ite_true] using hs a
      · simp [h, uniformProb]
    _ = uniformProb E*c := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      unfold uniformProb
      ring
-- CHECKPOINT

/-- Condition on every coordinate except one, retaining the primary event. -/
theorem probability_and_update_le {I V : Type*} [Fintype I] [Fintype V]
    [Nonempty V] [DecidableEq I] (E F : (I → V) → Prop) (i : I) (c : ℚ≥0)
    (hE : ∀ k v, E (Function.update k i v) ↔ E k)
    (hs : ∀ k, uniformProb (fun v => F (Function.update k i v)) ≤ c) :
    uniformProb (fun k => E k ∧ F k) ≤ uniformProb E*c := by
  classical
  let e := (Equiv.funSplitAt i V).trans (Equiv.prodComm _ _)
  let v₀ : V := Classical.choice inferInstance
  let base (r : {j // j ≠ i} → V) := e.symm (r,v₀)
  have hu (r : {j // j ≠ i} → V) (v : V) :
      e.symm (r,v) = Function.update (base r) i v := by
    funext j
    by_cases hj : j = i
    · subst j; simp [e, base]
    · simp [e, base, Function.update, hj]
  have he (r : {j // j ≠ i} → V) (v : V) :
      E (e.symm (r,v)) ↔ E (base r) := by
    rw [hu]
    exact hE _ _
  have hb : uniformProb (fun r => E (base r)) = uniformProb E := by
    calc
      _ = uniformProb (fun rv : ({j // j ≠ i} → V) × V => E (base rv.1)) :=
        (Classic.uniformProb_ignore_right _).symm
      _ = uniformProb (fun rv => E (e.symm rv)) :=
        congrArg uniformProb (funext fun ⟨r,v⟩ => propext (he r v).symm)
      _ = uniformProb E := uniformProb_equiv e.symm E
  rw [← uniformProb_equiv e.symm (fun k => E k ∧ F k)]
  calc
    _ = uniformProb (fun rv => E (base rv.1) ∧ F (e.symm rv)) :=
      congrArg uniformProb (funext fun ⟨r,v⟩ => propext (and_congr (he r v) Iff.rfl))
    _ ≤ uniformProb (fun r => E (base r))*c := by
      apply probability_and_prod_le
      intro r
      have hf : (fun v => F (e.symm (r,v))) =
          (fun v => F (Function.update (base r) i v)) :=
        funext fun v => congrArg F (hu r v)
      rw [hf]
      exact hs (base r)
    _ = _ := by rw [hb]
-- CHECKPOINT

end ProvenHashes.UMASH
