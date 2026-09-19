import ProvenHashes.UMASHLongIdentity
import ProvenHashes.UMASHShortClosure

namespace ProvenHashes.UMASH
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem finalize_unfinalize (x : Word) : finalize (unfinalize x) = x := by
  obtain ⟨y,rfl⟩ := (Finite.surjective_of_injective finalize_injective) x
  rw [unfinalize_finalize]
-- CHECKPOINT

theorem short_unfinalized_uniform (seed : Word) (m : Message) (hm : m.length ≤ 8) (t : Word) :
    uniformProb (fun k : OHKey => unfinalize (shortHash k seed m false) = t) = (1:ℚ≥0)/q := by
  have he : (fun k : OHKey => unfinalize (shortHash k seed m false) = t) =
      (fun k => shortHash k seed m false = finalize t) := by
    funext k
    apply propext
    constructor
    · intro h
      simpa only [finalize_unfinalize] using congrArg finalize h
    · intro h
      rw [h, unfinalize_finalize]
  rw [he]
  exact short_message_uniform seed m hm (finalize t)
-- CHECKPOINT

theorem short_constant_probability (seed : Word) (m : Message) (hm : m.length ≤ 8) :
    uniformProb (fun k : OHKey => ((unfinalize (shortHash k seed m false)).toNat : Field) = 0) ≤
      (9:ℚ≥0)/q := by
  classical
  let T := Finset.univ.filter (fun t : Word => (t.toNat : Field) = 0)
  let E (t : Word) (k : OHKey) := unfinalize (shortHash k seed m false) = t
  calc
    _ ≤ uniformProb (fun k : OHKey => ∃ t ∈ T, E t k) := by
      apply probability_mono
      intro k hk
      exact ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
    _ ≤ ∑ t ∈ T, uniformProb (E t) := probability_union_bound T E
    _ ≤ ∑ _t ∈ T, (1:ℚ≥0)/q :=
      Finset.sum_le_sum (fun t _ => (short_unfinalized_uniform seed m hm t).le)
    _ = T.card/(q:ℚ≥0) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (9:ℚ≥0)/q := div_le_div_of_nonneg_right (Nat.cast_le.mpr (field_word_fibre 0)) (by positivity)
-- CHECKPOINT

theorem short_long_identity_probability (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : 8 < y.length) :
    uniformProb (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y) ≤
      (9:ℚ≥0)/q := by
  apply (probability_mono ?_).trans (short_constant_probability seed x hx)
  intro k hk
  have he := congrArg (fun P : Polynomial Field => P.coeff 0) hk
  simpa only [comparisonPolynomial, if_pos hx, if_neg (by omega : ¬y.length ≤ 8),
    Polynomial.coeff_C_zero, blockPolynomial_constant] using he
-- CHECKPOINT

/-- Lemma 8.4, with the long-message qualification required by the corrected assembly. -/
theorem iid_long_primary_identity_bound : IIDLongPrimaryIdentityBound := by
  intro seed x y hne hlong
  by_cases hx : 8 < x.length
  · by_cases hy : 8 < y.length
    · by_cases hc : (encode x).length = (encode y).length
      · exact same_block_count_identity_bound seed x y hx hy hne hc
      · exact (corrected_different_block_counts_bound seed x y hx hy hc).le.trans
          (by apply NNRat.coe_le_coe.mp; norm_num [q])
    · have h := short_long_identity_probability seed y x (by omega) hx
      have h' := h.trans (show (9:ℚ≥0)/q ≤ (364816:ℚ≥0)/q from
        by apply NNRat.coe_le_coe.mp; norm_num [q])
      simpa only [eq_comm] using h'
  · have hy : 8 < y.length := hlong.resolve_left hx
    exact (short_long_identity_probability seed x y (by omega) hy).trans
      (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

theorem long_primary_identity_bound : LongPrimaryIdentityBound :=
  long_identity_of_iid iid_long_primary_identity_bound
-- CHECKPOINT

end ProvenHashes.UMASH
