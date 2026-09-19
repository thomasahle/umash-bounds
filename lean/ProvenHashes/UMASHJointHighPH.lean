import ProvenHashes.UMASHJointLowPH
import ProvenHashes.UMASHEvenPHSlice

namespace ProvenHashes.UMASH
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype ph clmul maskSet chunkCode

theorem projected_collision_equal_low_bound {K : Type*} [Fintype K]
    (x y : K → Chunk)
    (hinj : Function.Injective (fun k => chunkCode (x k)+chunkCode (y k)))
    (hlow : ∀ k, project (x k) = project (y k) → (x k).1 = (y k).1) :
    uniformProb (fun k => project (x k) = project (y k)) ≤
      (852:ℚ≥0)/(Fintype.card K : ℚ≥0) := by
  classical
  let T := ({0}:Finset ℕ) ×ˢ maskSet
  have h := injective_target_probability
    (fun k => ((x k).1.toNat ^^^ (y k).1.toNat, (x k).2.toNat ^^^ (y k).2.toNat))
    (chunkCode_xor_nat_injective x y hinj) T
    (fun k => project (x k) = project (y k)) ?_
  · simpa only [T, Finset.card_product, Finset.card_singleton, one_mul, maskSet_card,
      Nat.cast_ofNat] using h
  · intro k hk
    apply Finset.mem_product.mpr
    constructor
    · dsimp only
      rw [hlow k hk, Nat.xor_self]
      exact Finset.mem_singleton_self _
    · exact (Finset.mem_product.mp (project_eq_mask_cover (x k) (y k) hk)).2
-- CHECKPOINT

theorem masked_ph_high_valuation_probability (x y M N : Chunk)
    (hne : x ≠ y) (hx : 16 ∣ (x.1 ^^^ y.1).toNat) (hy : 16 ∣ (x.2 ^^^ y.2).toNat)
    (hm : M.1 = N.1) :
    uniformProb (fun k : Chunk => project (xorChunk M (ph k x)) =
      project (xorChunk N (ph k y))) ≤ (852:ℚ≥0)/q := by
  have hlow (k : Chunk)
      (hk : project (xorChunk M (ph k x)) = project (xorChunk N (ph k y))) :
      (xorChunk M (ph k x)).1 = (xorChunk N (ph k y)).1 := by
    have hM : 2^4 ∣ (M.1 ^^^ N.1).toNat := by simp [hm]
    have hpre := (word_prefix_eq_iff_xor_dvd _ _ 4).mpr
      (masked_ph_low_prefix x y M N k 4 (by decide) hx hy hM)
    have he := congrArg (fun z : Field × Field => z.1.val) hk
    simp only [project, ZMod.val_natCast] at he
    apply BitVec.eq_of_toNat_eq
    exact congruent_equal_low_four _ _ (xorChunk M (ph k x)).1.isLt
      (xorChunk N (ph k y)).1.isLt he hpre
  have hs (f g : Word → Chunk)
      (hi : Function.Injective (fun v => chunkCode (f v)+chunkCode (g v)))
      (hl : ∀ v, project (xorChunk M (f v)) = project (xorChunk N (g v)) →
        (xorChunk M (f v)).1 = (xorChunk N (g v)).1) :
      uniformProb (fun v => project (xorChunk M (f v)) = project (xorChunk N (g v))) ≤
        (852:ℚ≥0)/q := by
    have hinj : Function.Injective (fun v =>
        chunkCode (xorChunk M (f v))+chunkCode (xorChunk N (g v))) := by
      intro a b hab
      apply hi
      simp only [chunkCode_xor] at hab
      have hh := congrArg (fun z : ChunkCode => z-(chunkCode M+chunkCode N)) hab
      convert hh using 1 <;> abel
    simpa only [word_card] using projected_collision_equal_low_bound _ _ hinj hl
  by_cases hx' : x.1 ≠ y.1
  · apply probability_prod_le
    intro fixed
    exact hs _ _ (ph_code_slice_right x y hx' fixed) (fun v => hlow (fixed,v))
  · have hy' : x.2 ≠ y.2 := fun h => hne (Prod.ext (not_ne_iff.mp hx') h)
    rw [← uniformProb_equiv (Equiv.prodComm Word Word)
      (fun k : Chunk => project (xorChunk M (ph k x)) = project (xorChunk N (ph k y)))]
    apply probability_prod_le
    intro fixed
    exact hs _ _ (ph_code_slice_left x y hy' fixed) (fun v => hlow (v,fixed))
-- CHECKPOINT

end ProvenHashes.UMASH
