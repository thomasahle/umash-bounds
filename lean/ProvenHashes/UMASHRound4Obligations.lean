import ProvenHashes.UMASHLowCoordinates

/-! The single remaining analytic term in PROOF2 Lemma 5.2, and the
checked assembly using it. This is an explicit proposition, not an axiom. -/
namespace ProvenHashes.UMASH

/-- PROOF2 (17), third term, for nonzero targets with the trimmed hypotheses. -/
def LowENHQuadraticBound : Prop := ∀ (δ ε r e : ℕ),
  0 < δ → δ < q → 0 < ε → ε < q →
  r = min (padicValNat 2 δ) (padicValNat 2 ε) →
  1 ≤ r → 0 < e → e < q → 2^r ∣ e →
  uniformProb (fun ab : Word × Word => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
    (4:ℚ≥0)*2^r*2^(((maskBitSet 64 e).card+1)/2)/q

/-- All remaining work in Lemma 5.2 is exposed as its quadratic term;
the zero, sparse, and dense terms are closed theorems. -/
theorem low_enh_target_bound_of_quadratic (hquad : LowENHQuadraticBound) :
    LowENHTargetBound := by
  intro δ ε r e hδ₀ hδ hε₀ hε hr hr1 he hd
  by_cases he0 : e = 0
  · subst e
    rw [low_xor_zero_probability δ ε r ⟨hδ₀,hδ⟩ ⟨hε₀,hε⟩ hr]
    simp only [lowTargetK, if_pos rfl]
    rfl
  · have hq : (0:ℚ≥0) < q := by norm_num [q]
    rw [lowTargetK, if_neg he0]
    apply (le_div_iff₀ hq).mpr
    refine le_min ((le_div_iff₀ hq).mp
      (low_xor_sparse_probability δ ε r e ⟨hδ₀,hδ⟩ ⟨hε₀,hε⟩ hr)) (le_min ?_ ?_)
    · exact (le_div_iff₀ hq).mp
        (low_xor_dense_probability δ ε r e ⟨hδ₀,hδ⟩ ⟨hε₀,hε⟩ hr hr1 hd)
    · exact (le_div_iff₀ hq).mp
        (hquad δ ε r e hδ₀ hδ hε₀ hε hr hr1 (Nat.pos_of_ne_zero he0) he hd)
-- CHECKPOINT

end ProvenHashes.UMASH
