import ProvenHashes.UMASHMessageJointBounds
import ProvenHashes.UMASHJointMixture

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem fingerprint_multiplier_slice (L : ℕ) (k : OHKey) (seed : Word) (x y : Message)
    (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L) :
    uniformProb (fun f : PolyKey × PolyKey =>
      hashWith k f.1.val.val seed x false = hashWith k f.1.val.val seed y false ∧
      hashWith k f.2.val.val seed x true = hashWith k f.2.val.val seed y true) ≤
      (if modePolynomial false k seed x = modePolynomial false k seed y then 1 else rootRate L)*
      (if modePolynomial true k seed x = modePolynomial true k seed y then 1 else rootRate L) := by
  let P (mode : Bool) := modePolynomial mode k seed x - modePolynomial mode k seed y
  have hd (mode : Bool) : (P mode).natDegree ≤ 2*((L+31)/32) :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le
      (modePolynomial_degree L mode k seed x hx) (modePolynomial_degree L mode k seed y hy))
  have hm : uniformProb (fun f : PolyKey × PolyKey =>
      hashWith k f.1.val.val seed x false = hashWith k f.1.val.val seed y false ∧
      hashWith k f.2.val.val seed x true = hashWith k f.2.val.val seed y true) ≤
      uniformProb (fun f : PolyKey × PolyKey => (P false).eval (f.1.val.val:Field) = 0 ∧
        (P true).eval (f.2.val.val:Field) = 0) := by
    apply probability_mono
    intro f hf
    simp only [P,Polynomial.eval_sub,sub_eq_zero,modePolynomial_eval]
    exact ⟨congrArg (fun a => ((unfinalize a).toNat:Field)) hf.1,
      congrArg (fun a => ((unfinalize a).toNat:Field)) hf.2⟩
  apply hm.trans
  simpa only [P,sub_eq_zero,Nat.cast_mul,Nat.cast_ofNat,rootRate] using
    independent_polynomial_root_product (P false) (P true) (2*((L+31)/32)) (hd false) (hd true)
-- CHECKPOINT

theorem iid_long_fingerprint_probability (L : ℕ) (seed : Word) (x y : Message)
    (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L) (hne : x ≠ y)
    (hlong : 8 < x.length ∨ 8 < y.length) :
    uniformProb (fun k : OHKey × (PolyKey × PolyKey) =>
      hashWith k.1 k.2.1.val.val seed x false = hashWith k.1 k.2.1.val.val seed y false ∧
      hashWith k.1 k.2.2.val.val seed x true = hashWith k.1 k.2.2.val.val seed y true) ≤
      (rootRate L)^2+rootRate L*((364816+729632:ℚ≥0)/q)+(1:ℚ≥0)/2^87 := by
  have hm := probability_joint_mixture
    (fun k : OHKey × (PolyKey × PolyKey) =>
      hashWith k.1 k.2.1.val.val seed x false = hashWith k.1 k.2.1.val.val seed y false ∧
      hashWith k.1 k.2.2.val.val seed x true = hashWith k.1 k.2.2.val.val seed y true)
    (fun k => modePolynomial false k seed x = modePolynomial false k seed y)
    (fun k => modePolynomial true k seed x = modePolynomial true k seed y)
    (rootRate L) (fun k => by
      have h := fingerprint_multiplier_slice L k seed x y hx hy
      by_cases h0 : modePolynomial false k seed x = modePolynomial false k seed y <;>
        by_cases h1 : modePolynomial true k seed x = modePolynomial true k seed y <;>
        simpa only [h0,h1,ite_true,ite_false] using h)
  apply hm.trans
  apply add_le_add
  · apply add_le_add_left
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [modePolynomial_primary,add_div] using
      add_le_add (iid_long_primary_identity_bound seed x y hne hlong)
        (message_secondary_identity_probability seed x y hne hlong)
  · exact (message_joint_identity_probability seed x y hne hlong).trans
      (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

/-- Conditioning only the OH coordinates also applies to the independent
multiplier product without altering its architecture. -/
theorem distinct_product_probability_le {B : Type*} [Fintype B] [Nonempty B]
    (E : OHKey × B → Prop) (C : ℚ≥0) (hE : uniformProb E ≤ C) :
    uniformProb (fun k : DistinctOHKey × B => E (k.1.val,k.2)) ≤ C/(((q-561:ℕ):ℚ≥0)/q) := by
  classical
  let A := fun k : OHKey × B => Function.Injective k.1
  let equiv : (DistinctOHKey × B) ≃ {k : OHKey × B // A k} :=
    { toFun := fun k => ⟨(k.1.val,k.2),k.1.property⟩
      invFun := fun k => (⟨k.val.1,k.property⟩,k.val.2)
      left_inv := by intro k; rfl
      right_inv := by intro k; rfl }
  letI : Nonempty {k : OHKey × B // A k} :=
    ⟨equiv (Classical.choice (inferInstance : Nonempty (DistinctOHKey × B)))⟩
  have hA : ((q-561:ℕ):ℚ≥0)/q ≤ uniformProb A := by
    rw [Classic.uniformProb_ignore_right (fun k : OHKey => Function.Injective k)]
    exact distinct_key_acceptance
  have h := probability_subtype_le A E (((q-561:ℕ):ℚ≥0)/q) C (by norm_num [q]) hA hE
  rw [← uniformProb_equiv equiv (fun k => E k.val)] at h
  exact h
-- CHECKPOINT

theorem distinct_long_fingerprint_probability (L : ℕ) (seed : Word) (x y : Message)
    (hx : x.length ≤ 8*L) (hy : y.length ≤ 8*L) (hne : x ≠ y)
    (hlong : 8 < x.length ∨ 8 < y.length) :
    uniformProb (fun k : Key128 => hash128 k seed x = hash128 k seed y) ≤
      ((rootRate L)^2+rootRate L*((364816+729632:ℚ≥0)/q)+(1:ℚ≥0)/2^87)/
        (((q-561:ℕ):ℚ≥0)/q) := by
  have h := distinct_product_probability_le _ _ (iid_long_fingerprint_probability L seed x y hx hy hne hlong)
  simpa only [hash128,Prod.mk.injEq] using h
-- CHECKPOINT

end ProvenHashes.UMASH
