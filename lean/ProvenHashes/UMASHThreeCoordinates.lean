import ProvenHashes.UMASHJointProbability

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb

/-- Averaging over three distinct coordinates of a finite uniform function.
The pointwise slice may retain arbitrary dependence on every other key. -/
theorem probability_le_of_three_updates {I V : Type*} [Fintype I] [Fintype V]
    [Nonempty V] [DecidableEq I] (E : (I → V) → Prop) (i j k : I)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (bound : ℚ≥0)
    (hs : ∀ K, uniformProb (fun abc : V × (V × V) =>
      E (Function.update (Function.update (Function.update K i abc.1) j abc.2.1) k abc.2.2)) ≤ bound) :
    uniformProb E ≤ bound := by
  let swap : ((I → V) × (V × (V × V))) → ((I → V) × (V × (V × V))) :=
    fun z => (Function.update (Function.update (Function.update z.1 i z.2.1) j z.2.2.1) k z.2.2.2,
      (z.1 i, (z.1 j, z.1 k)))
  have hinv : Function.Involutive swap := by
    rintro ⟨K,a,b,c⟩
    apply Prod.ext
    · funext z
      by_cases hi : z = i
      · subst z
        simp [swap, Function.update_apply, hij, hik]
      · by_cases hj : z = j
        · subst z
          simp [swap, Function.update_apply, hij, hij.symm, hjk]
        · by_cases hk : z = k
          · subst z
            simp [swap, Function.update_apply, hik, hik.symm, hjk, hjk.symm]
          · simp [swap, Function.update_apply, hi, hj, hk]
    · simp [swap, Function.update_apply, hij, hij.symm, hik, hik.symm, hjk, hjk.symm]
  let e := hinv.toPerm
  calc
    uniformProb E = uniformProb (fun z : (I → V) × (V × (V × V)) => E z.1) :=
      (Classic.uniformProb_ignore_right E).symm
    _ = uniformProb (fun z : (I → V) × (V × (V × V)) => E (e z).1) :=
      (uniformProb_equiv e (fun z => E z.1)).symm
    _ ≤ bound := probability_prod_le _ bound hs
-- CHECKPOINT

/-- A raw-target partition followed by a conditional independent noise
estimate. This is a finite counting identity, with no stochastic axioms. -/
theorem probability_partition_prod_le {A B T : Type*} [Fintype A] [Fintype B]
    (E : A × B → Prop) (F : T → A → Prop) (targets : Finset T)
    (count weight : T → ℚ≥0)
    (hcover : ∀ a b, E (a,b) → ∃ t ∈ targets, F t a)
    (hslice : ∀ t ∈ targets, ∀ a, F t a → uniformProb (fun b => E (a,b)) ≤ weight t)
    (hcount : ∀ t ∈ targets, uniformProb (F t) ≤ count t) :
    uniformProb E ≤ ∑ t ∈ targets, count t*weight t := by
  calc
    _ ≤ uniformProb (fun ab => ∃ t ∈ targets, F t ab.1 ∧ E ab) := by
      apply probability_mono
      rintro ⟨a,b⟩ h
      obtain ⟨t,ht,hF⟩ := hcover a b h
      exact ⟨t,ht,hF,h⟩
    _ ≤ ∑ t ∈ targets, uniformProb (fun ab => F t ab.1 ∧ E ab) := probability_union_bound _ _
    _ ≤ ∑ t ∈ targets, count t*weight t := by
      apply Finset.sum_le_sum
      intro t ht
      have hcond : ∀ a, uniformProb (fun b => F t a ∧ E (a,b)) ≤ weight t := by
        intro a
        by_cases ha : F t a
        · simpa only [ha, true_and] using hslice t ht a ha
        · simp [ha, uniformProb]
      have h := probability_and_prod_le (F t) (fun ab => F t ab.1 ∧ E ab) (weight t) hcond
      simp only [and_self_left] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hcount t ht) (zero_le _))
-- CHECKPOINT

end ProvenHashes.UMASH
