import ProvenHashes.UMASHShortProbability
import ProvenHashes.UMASHShortPacking

namespace ProvenHashes.UMASH
attribute [local irreducible] uniformProb wordFintype

theorem short_collision_iid (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : y.length ≤ 8) (hxy : x ≠ y) :
    uniformProb (fun k : OHKey => shortHash k seed x false = shortHash k seed y false) ≤
      (1:ℚ≥0)/q := by
  classical
  by_cases hl : x.length = y.length
  · have he : (fun k : OHKey => shortHash k seed x false = shortHash k seed y false) =
        (fun _ : OHKey => False) := by
      funext k
      exact propext ⟨fun h => hxy (short_equal_length_injective seed k x y hx hl h),
        False.elim⟩
    rw [he]
    simp only [uniformProb, Finset.filter_false, Finset.card_empty, Nat.cast_zero,
      zero_div, zero_le]
  · exact (short_different_length_collision seed x y hx hy hl).le
-- CHECKPOINT

theorem short_one_word_bound : ShortOneWordBound := by
  intro seed x y hx hy hxy
  have h := distinct_probability_le
    (fun k : OHKey => shortHash k seed x false = shortHash k seed y false)
    1 (short_collision_iid seed x y hx hy hxy)
  simp only [hash64, hashWith, hx, hy, ↓reduceIte]
  let E : DistinctOHKey → Prop := fun k =>
    shortHash k.val seed x false = shortHash k.val seed y false
  change uniformProb (fun k : DistinctOHKey × PolyKey => E k.1) ≤ _
  rw [Classic.uniformProb_ignore_right E]
  exact h
-- CHECKPOINT

theorem certified64_of_iid_long (h : IIDLongPrimaryIdentityBound) : CertifiedAllPairs64 :=
  certified64_of_iid_long_and_short h short_one_word_bound
-- CHECKPOINT

end ProvenHashes.UMASH
