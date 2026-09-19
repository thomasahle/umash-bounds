import ProvenHashes.UMASHSharpObligations
import ProvenHashes.UMASHShortLongIdentity

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem same_block_count_identity_bound3125 (hblock : PrimaryBlockBound3125) (seed : Word) (x y : Message)
    (hx : 8 < x.length) (hy : 8 < y.length) (hne : x ≠ y)
    (hc : (encode x).length = (encode y).length) :
    uniformProb (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y) ≤
      (3125:ℚ≥0)/q := by
  have henc : encode x ≠ encode y := fun h => hne (encoding_injective_long x y hx hy h)
  have hwit : ∃ i : Fin (encode x).length,
      (encode x)[i.val] ≠ (encode y)[i.val]'(by rw [← hc]; exact i.isLt) := by
    by_contra hn
    push_neg at hn
    apply henc
    apply List.ext_getElem hc
    intro i hi hiy
    exact hn ⟨i,hi⟩
  obtain ⟨i,hib⟩ := hwit
  let bx := (encode x)[i.val]
  let byy := (encode y)[i.val]'(by rw [← hc]; exact i.isLt)
  have hvx : bx.Valid := encoded_blocks_valid x bx (List.getElem_mem i.isLt)
  have hvy : byy.Valid := encoded_blocks_valid y byy (List.getElem_mem (by rw [← hc]; exact i.isLt))
  have htuple : bx.chunks ≠ byy.chunks ∨ blockTag seed bx ≠ blockTag seed byy := by
    by_contra hn
    push_neg at hn
    exact hib (valid_block_eq_of_tuple seed bx byy hvx hvy hn.1 hn.2)
  apply (probability_mono ?_).trans (hblock seed bx byy hvx hvy htuple)
  intro k hk
  have hxshort : ¬x.length ≤ 8 := by omega
  have hyshort : ¬y.length ≤ 8 := by omega
  have he : blockPolynomial (compress false k seed x) = blockPolynomial (compress false k seed y) := by
    simpa only [comparisonPolynomial, hxshort, hyshort, ↓reduceIte] using hk
  have hlen : (compress false k seed x).length = (compress false k seed y).length := by
    simpa only [compress, List.length_map] using hc
  have hp := blockPolynomial_same_length _ _ hlen he
  have hi : i.val < ((compress false k seed x).map project).length := by
    simpa only [List.length_map, compress] using i.isLt
  have hget := List.getElem_of_eq hp hi
  simpa only [compress, List.getElem_map, Bool.false_eq_true, ↓reduceIte,
    primaryEvent, bx, byy] using hget
-- CHECKPOINT

/-- Lemma 8.4, with the long-message qualification required by the corrected assembly. -/
theorem iid_long_identity3125_of_block (hblock : PrimaryBlockBound3125) : IIDLongPrimaryIdentityBound3125 := by
  intro seed x y hne hlong
  by_cases hx : 8 < x.length
  · by_cases hy : 8 < y.length
    · by_cases hc : (encode x).length = (encode y).length
      · exact same_block_count_identity_bound3125 hblock seed x y hx hy hne hc
      · exact (corrected_different_block_counts_bound seed x y hx hy hc).le.trans
          (by apply NNRat.coe_le_coe.mp; norm_num [q])
    · have h := short_long_identity_probability seed y x (by omega) hx
      have h' := h.trans (show (9:ℚ≥0)/q ≤ (3125:ℚ≥0)/q from
        by apply NNRat.coe_le_coe.mp; norm_num [q])
      simpa only [eq_comm] using h'
  · have hy : 8 < y.length := hlong.resolve_left hx
    exact (short_long_identity_probability seed x y (by omega) hy).trans
      (by apply NNRat.coe_le_coe.mp; norm_num [q])
-- CHECKPOINT

theorem long_identity3125_of_iid (h : IIDLongPrimaryIdentityBound3125) :
    LongPrimaryIdentityBound3125 := by
  intro seed x y hxy hlong
  exact distinct_probability_le
    (fun k : OHKey => comparisonPolynomial k seed x = comparisonPolynomial k seed y)
    3125 (h seed x y hxy hlong)
-- CHECKPOINT

theorem short_bound_le_certifiedEnvelope3125 (L : ℕ) :
    (1:ℚ≥0)/(q-561 : ℕ) ≤ certifiedEnvelope3125 L := by
  by_cases h : L = 1
  · simp only [certifiedEnvelope3125, if_pos h, le_refl]
  · rw [certifiedEnvelope3125, if_neg h]
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    apply NNRat.coe_le_coe.mp
    norm_num [sharpA, q]
-- CHECKPOINT

/-- The corrected assembly uses actual short/short collisions and invokes the
polynomial-identity premise only when at least one message is long. -/
theorem certified64_3125_of_long_identity_and_short (h : LongPrimaryIdentityBound3125)
    (hs : ShortOneWordBound) : CertifiedAllPairs64_3125 := by
  intro L seed x y _hL hx hy hxy
  by_cases hshort : x.length ≤ 8 ∧ y.length ≤ 8
  · exact (hs seed x y hshort.1 hshort.2 hxy).trans (short_bound_le_certifiedEnvelope3125 L)
  · have hlong : 8 < x.length ∨ 8 < y.length := by omega
    have hL : L ≠ 1 := by intro he; subst L; simp only [mul_one] at hx hy; omega
    have hc : 1-sharpA = sharpComplement :=
      tsub_eq_of_eq_add (sharpA_add_complement.symm.trans (add_comm _ _))
    rw [certifiedEnvelope3125, if_neg hL, ← hc]
    apply probability_mixture _
      (fun k : DistinctOHKey => comparisonPolynomial k.val seed x = comparisonPolynomial k.val seed y)
      (rootRate L) sharpA (min_le_left _ _) (h seed x y hxy hlong)
    intro k hk
    exact comparison_slice_bound L k.val seed x y hx hy hk
-- CHECKPOINT

/-- This interface retains an explicit block-bound premise until the three
new block cases have been proved. Short/short uses actual collisions. -/
theorem certified64_3125_of_block (h : PrimaryBlockBound3125) : CertifiedAllPairs64_3125 :=
  certified64_3125_of_long_identity_and_short
    (long_identity3125_of_iid (iid_long_identity3125_of_block h)) short_one_word_bound
-- CHECKPOINT

theorem certified128_3125_of_64 (h : CertifiedAllPairs64_3125) : CertifiedAllPairs128_3125 := by
  intro L seed x y hL hx hy hxy
  exact (fingerprint_collision_le_primary seed x y).trans (h L seed x y hL hx hy hxy)
-- CHECKPOINT

theorem correctedLinear64_423_of_certified (h : CertifiedAllPairs64_3125) : CorrectedLinear64_423 := by
  intro L seed x y hL hx hy hxy
  exact (h L seed x y hL hx hy hxy).trans (certifiedEnvelope3125_le_linear L hL)
-- CHECKPOINT

theorem correctedLinear128_423_of_64 (h : CorrectedLinear64_423) : CorrectedLinear128_423 := by
  intro L seed x y hL hx hy hxy
  exact (fingerprint_collision_le_primary seed x y).trans (h L seed x y hL hx hy hxy)
-- CHECKPOINT

end ProvenHashes.UMASH
