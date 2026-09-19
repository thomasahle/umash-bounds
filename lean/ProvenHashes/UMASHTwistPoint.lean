import ProvenHashes.UMASHTwistWeights
import ProvenHashes.UMASHJointLengths

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul

theorem twist_low_full_mask : twistLowFactor (q-1) = (33:ℚ≥0)/q := by
  decide +kernel
-- CHECKPOINT

/-- Every low PH point has probability at most 33/q, retaining an arbitrary
fixed checksum and XOR offset. -/
theorem twist_low_point_probability (checksum : Chunk) (offset t : Word) :
    uniformProb (fun k : Chunk => offset ^^^ (ph k checksum).1 = t) ≤ (33:ℚ≥0)/q := by
  have h := twist_low_pattern_probability checksum offset (q-1) t.toNat
  rw [twist_low_full_mask] at h
  apply (probability_mono ?_).trans h
  intro k hk
  rw [hk]
  change t.toNat &&& (2^64-1) = t.toNat
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt t.isLt]
-- CHECKPOINT

theorem twist_low_field_point_probability (checksum : Chunk) (offset : Word) (t : Field) :
    uniformProb (fun k : Chunk => ((offset ^^^ (ph k checksum).1).toNat : Field) = t) ≤
      (297:ℚ≥0)/q := by
  let T := Finset.univ.filter (fun w : Word => (w.toNat : Field) = t)
  let E (w : Word) (k : Chunk) := offset ^^^ (ph k checksum).1 = w
  calc
    _ ≤ uniformProb (fun k : Chunk => ∃ w ∈ T, E w k) := by
      apply probability_mono
      intro k hk
      exact ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩,rfl⟩
    _ ≤ ∑ w ∈ T, uniformProb (E w) := probability_union_bound T E
    _ ≤ ∑ _w ∈ T, (33:ℚ≥0)/q :=
      Finset.sum_le_sum (fun w _ => twist_low_point_probability checksum offset w)
    _ = T.card*((33:ℚ≥0)/q) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 9*((33:ℚ≥0)/q) := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (field_word_fibre t)) (by positivity)
    _ = _ := by ring
-- CHECKPOINT

end ProvenHashes.UMASH
