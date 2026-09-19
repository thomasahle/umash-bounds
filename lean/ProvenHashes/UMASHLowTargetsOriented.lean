import ProvenHashes.UMASHLowTargetQuadratic

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb

/-- The quadratic low-target estimate allows a zero second increment. -/
theorem low_quadratic_probability_oriented (δ ε r e : ℕ)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (ha : (δ/2^r)%2 = 1)
    (he : 0 < e ∧ e < q) (hd : 2^r ∣ e) :
    uniformProb (fun ab : Chunk => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      (4:ℚ≥0)*2^r*2^(((maskBitSet 64 e).card+1)/2)/q := by
  have hrv : r ≤ padicValNat 2 e := by
    by_contra h
    exact pow_succ_padicValNat_not_dvd (p := 2) he.1.ne'
      ((pow_dvd_pow 2 (by omega : padicValNat 2 e+1 ≤ r)).trans hd)
  let equiv : (Fin (2^64) × Fin (2^64)) ≃ Chunk :=
    Equiv.prodCongr BitVec.equivFin.symm.toEquiv BitVec.equivFin.symm.toEquiv
  rw [← uniformProb_equiv equiv]
  have hc := low_xor_quadratic_probability 64 r (δ/2^r) (ε/2^r) e he hrv ha
  simpa only [Nat.mul_div_cancel' hδ,Nat.mul_div_cancel' hε] using hc
-- CHECKPOINT

/-- All three terms of the low target bound under divisibility and one
odd divided increment; the other increment is allowed to vanish. -/
theorem low_target_probability_oriented (δ ε r e : ℕ) (hr : r < 64) (hr1 : 1 ≤ r)
    (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε) (ha : (δ/2^r)%2 = 1)
    (he : e < q) (hd : 2^r ∣ e) :
    uniformProb (fun ab : Chunk => lowENHXor 64 δ ε ab.1.toNat ab.2.toNat = e) ≤
      lowTargetK r e/q := by
  by_cases he0 : e = 0
  · subst e
    rw [low_xor_zero_probability_oriented r δ ε hr hδ hε ha]
    simp only [lowTargetK,if_pos rfl]
    rfl
  · have hq : (0:ℚ≥0) < q := by norm_num [q]
    have h2 : 2 ∣ 2^r := by simpa only [pow_one] using pow_dvd_pow 2 hr1
    rw [lowTargetK,if_neg he0]
    apply (le_div_iff₀ hq).mpr
    refine le_min ((le_div_iff₀ hq).mp
      (low_xor_sparse_probability_oriented r δ ε e hr hδ hε ha)) (le_min ?_ ?_)
    · exact (le_div_iff₀ hq).mp
        (low_xor_dense_probability_even δ ε e (h2.trans hδ) (h2.trans hε) (h2.trans hd))
    · exact (le_div_iff₀ hq).mp
        (low_quadratic_probability_oriented δ ε r e hδ hε ha ⟨Nat.pos_of_ne_zero he0,he⟩ hd)
-- CHECKPOINT

end ProvenHashes.UMASH
