import ProvenHashes.UMASHCorrectedAssembly

namespace ProvenHashes.UMASH
open scoped Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb

/-- Uniform sampling from a subtype is exactly conditioning the original
uniform distribution on its predicate. -/
theorem probability_subtype_mul {K : Type*} [Fintype K] [Nonempty K]
    (A E : K → Prop) [Fintype {k // A k}] [Nonempty {k // A k}] :
    uniformProb (fun k : {k // A k} => E k.val) * uniformProb A =
      uniformProb (fun k => A k ∧ E k) := by
  classical
  have he : (Finset.univ.filter (fun k : {k // A k} => E k.val)).card =
      (Finset.univ.filter (fun k => A k ∧ E k)).card := by
    apply Finset.card_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.property,
        (Finset.mem_filter.mp hk).2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro k hk
      have h := (Finset.mem_filter.mp hk).2
      exact ⟨⟨k, h.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩, rfl⟩
  have hK : (Fintype.card K : ℚ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : ((Finset.univ.filter A).card : ℚ≥0) ≠ 0 := by
    rw [← Fintype.card_subtype A]
    exact_mod_cast (Fintype.card_ne_zero (α := {k // A k}))
  unfold uniformProb
  rw [he, Fintype.card_subtype A]
  field_simp
  norm_cast
  apply congrArg Finset.card
  ext k
  simp
-- CHECKPOINT

theorem probability_subtype_le {K : Type*} [Fintype K] [Nonempty K]
    (A E : K → Prop) [Fintype {k // A k}] [Nonempty {k // A k}]
    (a b : ℚ≥0) (ha : 0 < a) (hA : a ≤ uniformProb A) (hE : uniformProb E ≤ b) :
    uniformProb (fun k : {k // A k} => E k.val) ≤ b/a := by
  apply (le_div_iff₀ ha).mpr
  calc
    _ ≤ uniformProb (fun k : {k // A k} => E k.val)*uniformProb A :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    _ = uniformProb (fun k => A k ∧ E k) := probability_subtype_mul A E
    _ ≤ uniformProb E := probability_mono (fun _ h => h.2)
    _ ≤ b := hE
-- CHECKPOINT

theorem distinct_probability_le (E : OHKey → Prop) (C : ℚ≥0)
    (h : uniformProb E ≤ C/q) :
    uniformProb (fun k : DistinctOHKey => E k.val) ≤ C/(q-561 : ℕ) := by
  have hb := probability_subtype_le (fun k : OHKey => Function.Injective k) E
    (((q-561 : ℕ) : ℚ≥0)/q) (C/q) (by norm_num [q]) distinct_key_acceptance h
  apply hb.trans_eq
  norm_num [q, div_eq_mul_inv]
  ring
-- CHECKPOINT

theorem long_identity_of_iid (h : IIDLongPrimaryIdentityBound) : LongPrimaryIdentityBound := by
  intro seed x y hxy hlong
  exact distinct_probability_le
    (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y)
    364816 (h seed x y hxy hlong)
-- CHECKPOINT

theorem certified64_of_iid_long_and_short (h : IIDLongPrimaryIdentityBound)
    (hs : ShortOneWordBound) : CertifiedAllPairs64 :=
  certified64_of_long_identity_and_short (long_identity_of_iid h) hs
-- CHECKPOINT

end ProvenHashes.UMASH
