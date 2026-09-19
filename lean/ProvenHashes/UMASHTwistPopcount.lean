import ProvenHashes.UMASHJointLedger

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

/-- Removing j low positions can remove at most j selected mask bits. -/
theorem mask_bit_set_suffix_card (n e j : ℕ) (hj : j ≤ n) :
    (maskBitSet n e).card ≤ j+(maskBitSet (n-j) (e/2^j)).card := by
  let S := maskBitSet n e
  have hlo : (S.filter (fun i => i.val < j)).card ≤ j := by
    calc
      _ ≤ (Finset.range j).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val)
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
        · intro a _ b _ hab
          exact Fin.ext hab
      _ = _ := Finset.card_range j
  have hhi : (S.filter (fun i => ¬i.val < j)).card ≤ (maskBitSet (n-j) (e/2^j)).card := by
    calc
      _ ≤ ((maskBitSet (n-j) (e/2^j)).image Fin.val).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val-j)
        · intro i hi
          have hji : j ≤ i.val := by have := (Finset.mem_filter.mp hi).2; omega
          have hbit : e.testBit i.val = true :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
          refine Finset.mem_image.mpr ⟨⟨i.val-j, by have := i.isLt; omega⟩, ?_, rfl⟩
          simp only [maskBitSet, Finset.mem_filter, Finset.mem_univ, true_and,
            Nat.testBit_div_two_pow, Nat.sub_add_cancel hji, hbit]
        · intro a ha b hb hab
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          change a.val-j = b.val-j at hab
          apply Fin.ext
          omega
      _ = _ := Finset.card_image_of_injective _ Fin.val_injective
  have hsplit : (S.filter (fun i => i.val < j)).card +
      (S.filter (fun i => ¬i.val < j)).card = S.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  dsimp only [S] at hlo hhi hsplit
  omega
-- CHECKPOINT

def twistLowPopcountFactor (h : ℕ) : ℚ≥0 :=
  1/q + ∑ j ∈ Finset.range 64, (2:ℚ≥0)^(63-j)*(1/2^(h-j))/q

/-- A suffix-count bound on the valuation-averaged twisting factor. -/
theorem twistLowFactor_le_popcount (e : ℕ) :
    twistLowFactor e ≤ twistLowPopcountFactor (maskBitSet 64 e).card := by
  unfold twistLowFactor twistLowPopcountFactor
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j hj
  have hj64 : j ≤ 64 := (Finset.mem_range.mp hj).le
  have hc : (maskBitSet 64 e).card-j ≤ (maskBitSet (64-j) (e/2^j)).card := by
    have := mask_bit_set_suffix_card 64 e j hj64
    omega
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℚ≥0) ≤ 2) hc)
-- CHECKPOINT

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The 65 possible popcounts give an exact elementary geometric sum. -/
theorem twist_low_popcount_factor_certificate : ∀ h : Fin 65,
    twistLowPopcountFactor h.val = ((h.val+2 : ℕ):ℚ≥0)/2^(h.val+1) := by
  decide +kernel
-- CHECKPOINT

def twistLowPopcountWeight (e : ℕ) : ℚ≥0 :=
  min 1 ((maskPatterns e).card *
    (((maskBitSet 64 e).card+2 : ℕ):ℚ≥0)/2^((maskBitSet 64 e).card+1))

/-- A simple popcount envelope for every exact low twisting weight. -/
theorem twistLowWeight_le_popcount (e : ℕ) :
    twistLowWeight e ≤ twistLowPopcountWeight e := by
  have hh : (maskBitSet 64 e).card < 65 := by
    have := mask_bit_set_card_le 64 e
    omega
  have hf := (twistLowFactor_le_popcount e).trans_eq
    (twist_low_popcount_factor_certificate ⟨(maskBitSet 64 e).card, hh⟩)
  unfold twistLowWeight twistLowPopcountWeight
  apply min_le_min le_rfl
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hf
    (show (0:ℚ≥0) ≤ (maskPatterns e).card by positivity)
-- CHECKPOINT

end ProvenHashes.UMASH
