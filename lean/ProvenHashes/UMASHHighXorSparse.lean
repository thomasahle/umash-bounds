import ProvenHashes.UMASHHighXorQuadratic
import ProvenHashes.UMASHAdditiveProductCore

namespace ProvenHashes.UMASH
open scoped BigOperators Classical

/-- Cross-wrap injectivity of the full product-difference residue gives
a stronger sparse-mask count than PROOF2 needs. Only one increment must
be nonzero; both operand wraps and arbitrary tags are retained. -/
theorem high_xor_sparse_count (n δ ε tag tag' e : ℕ) (S : Finset (ℕ × ℕ))
    (hδ : 0 < δ ∧ δ < 2^n) (hε : ε < 2^n)
    (hbox : ∀ ab ∈ S, ab.1 < 2^n ∧ ab.2 < 2^n)
    (hevent : ∀ ab ∈ S, highXorEventNat n δ ε tag tag' e ab) :
    S.card ≤ 2^(maskBitSet n e).card*2^n := by
  classical
  let f : ℕ × ℕ → ℕ × ℕ := fun ab => (ab.1, highXorPattern n tag e ab)
  calc
    _ ≤ ((Finset.range (2^n)) ×ˢ submaskTargets n e).card := by
      apply Finset.card_le_card_of_injOn f
      · intro ab hab
        apply Finset.mem_product.mpr
        refine ⟨Finset.mem_range.mpr (hbox ab hab).1, ?_⟩
        apply Finset.mem_filter.mpr
        dsimp only [f, highXorPattern]
        refine ⟨Finset.mem_range.mpr ?_, ?_⟩
        · exact Nat.and_le_left.trans_lt (Nat.mod_lt _ (by positivity))
        · rw [Nat.and_assoc, Nat.and_self]
      · rintro ⟨A,B₁⟩ h₁ ⟨A',B₂⟩ h₂ he
        have hA : A = A' := congrArg Prod.fst he
        subst A'
        have hz : highXorPattern n tag e (A,B₁) = highXorPattern n tag e (A,B₂) :=
          congrArg Prod.snd he
        have he₁ := hevent (A,B₁) h₁
        have he₂ := hevent (A,B₂) h₂
        have hp₁ := high_xor_product_residue (2^n) A B₁ ((A+δ)%2^n)
          ((B₁+ε)%2^n) tag tag' e he₁.1 he₁.2
        have hp₂ := high_xor_product_residue (2^n) A B₂ ((A+δ)%2^n)
          ((B₂+ε)%2^n) tag tag' e he₂.1 he₂.2
        unfold highXorPattern at hz
        rw [hz] at hp₁
        have hb₁ := hbox (A,B₁) h₁
        have hb₂ := hbox (A,B₂) h₂
        apply congrArg (fun B : ℕ => (A,B))
        exact wrapped_product_difference_unique (2^n) A ((A+δ)%2^n) ε B₁ B₂
          (by positivity) hb₁.1 (Nat.mod_lt _ (by positivity))
          (wrapped_add_ne (2^n) A δ hb₁.1 hδ.2 hδ.1.ne').symm hε hb₁.2 hb₂.2
          (hp₁.trans hp₂.symm)
    _ = 2^n*(submaskTargets n e).card := by rw [Finset.card_product, Finset.card_range]
    _ ≤ 2^n*2^(maskBitSet n e).card := Nat.mul_le_mul_left _ (submask_targets_card_le n e)
    _ = _ := Nat.mul_comm _ _
-- CHECKPOINT

theorem high_xor_sparse_probability (n δ ε tag tag' e : ℕ)
    (hδ : 0 < δ ∧ δ < 2^n) (hε : ε < 2^n) :
    uniformProb (fun ab : Fin (2^n) × Fin (2^n) =>
      highXorEventNat n δ ε tag tag' e (ab.1.val, ab.2.val)) ≤
      (2:ℚ≥0)^(maskBitSet n e).card/(2:ℚ≥0)^n := by
  have hc := fin_pair_probability_of_nat_count (2^n)
    (2^(maskBitSet n e).card*2^n) (highXorEventNat n δ ε tag tag' e)
    (fun S hb he => high_xor_sparse_count n δ ε tag tag' e S hδ hε hb he)
  calc
    _ ≤ ((2:ℚ≥0)^(maskBitSet n e).card*(2:ℚ≥0)^n)/((2:ℚ≥0)^n)^2 := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
    _ = _ := by field_simp
-- CHECKPOINT

theorem high_xor_sparse_probability_word (δ ε tag tag' e : ℕ)
    (hδ : 0 < δ ∧ δ < q) (hε : ε < q) :
    uniformProb (fun ab : Word × Word =>
      highXorEventNat 64 δ ε tag tag' e (ab.1.toNat, ab.2.toNat)) ≤
      (2:ℚ≥0)^(maskBitSet 64 e).card/q := by
  let equiv : (Fin (2^64) × Fin (2^64)) ≃ (Word × Word) :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  exact high_xor_sparse_probability 64 δ ε tag tag' e hδ hε
-- CHECKPOINT

end ProvenHashes.UMASH
