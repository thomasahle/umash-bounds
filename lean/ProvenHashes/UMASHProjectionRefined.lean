import ProvenHashes.UMASHProjection
import ProvenHashes.UMASHMaskRefinements

namespace ProvenHashes.UMASH
attribute [local irreducible] maskSet uniformProb

theorem mask_low_bit_count (b : Bool) :
    (maskSet.filter (fun d => d%2 = b.toNat)).card ≤ 604 := by
  cases b
  · rw [show Bool.toNat false = 0 from rfl, maskSet_low_high_counts.1]
    norm_num
  · rw [show Bool.toNat true = 1 from rfl, maskSet_low_high_counts.2.1]
-- CHECKPOINT

theorem mask_high_bit_count (b : Bool) :
    (maskSet.filter (fun d => d/2^63 = b.toNat)).card ≤ 604 := by
  cases b
  · rw [show Bool.toNat false = 0 from rfl, maskSet_low_high_counts.2.2.1]
    norm_num
  · rw [show Bool.toNat true = 1 from rfl, maskSet_low_high_counts.2.2.2]
-- CHECKPOINT

/-- The 604-squared transfer needed for an even PH difference.  The fixed-bit
premises are explicit, separate from slice injectivity. -/
theorem projected_collision_fixed_bits_bound {K : Type*} [Fintype K]
    (x y : K → Chunk) (b₀ b₆₃ : Bool)
    (hinj : Function.Injective (fun k =>
      ((x k).1.toNat ^^^ (y k).1.toNat, (x k).2.toNat ^^^ (y k).2.toNat)))
    (hlo : ∀ k, ((x k).1.toNat ^^^ (y k).1.toNat)%2 = b₀.toNat)
    (hhi : ∀ k, ((x k).2.toNat ^^^ (y k).2.toNat)/2^63 = b₆₃.toNat) :
    uniformProb (fun k => project (x k) = project (y k)) ≤
      (364816:ℚ≥0)/(Fintype.card K : ℚ≥0) := by
  classical
  let T := (maskSet.filter (fun d => d%2 = b₀.toNat)) ×ˢ
    (maskSet.filter (fun d => d/2^63 = b₆₃.toNat))
  have hc : T.card ≤ 364816 := by
    exact (Finset.card_product _ _).le.trans
      (Nat.mul_le_mul (mask_low_bit_count b₀) (mask_high_bit_count b₆₃))
  apply (injective_target_probability _ hinj T
    (fun k => project (x k) = project (y k)) ?_).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity))
  intro k hk
  have h := Finset.mem_product.mp (project_eq_mask_cover (x k) (y k) hk)
  exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h.1, hlo k⟩,
    Finset.mem_filter.mpr ⟨h.2, hhi k⟩⟩
-- CHECKPOINT

end ProvenHashes.UMASH
