import ProvenHashes.UMASHShufflerKernel
import ProvenHashes.UMASHRank
import ProvenHashes.UMASHEvenPHSlice

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
attribute [local irreducible] maskSet uniformProb wordFintype

/-- On the PH output subspace, the shuffler kernel has two elements. -/
theorem phShuffleWide_kernel_top_zero (s : ℕ) (hs : 0 < s) (x : Wide)
    (htop : x.getLsbD 127 = false) :
    phShuffleWide s x = 0 ↔ x = 0 ∨ x = BitVec.ofNat 128 (2^63) := by
  rw [phShuffleWide_kernel s hs]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr h
    · subst x
      change true = false at htop
      contradiction
    · subst x
      change true = false at htop
      contradiction
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
-- CHECKPOINT

/-- A shuffler fibre inside bit-127-zero words is determined by bit 63. -/
theorem phShuffleWide_fibre_bit63 (s : ℕ) (hs : 0 < s) (a b : Wide)
    (ha : a.getLsbD 127 = false) (hb : b.getLsbD 127 = false)
    (hS : phShuffleWide s a = phShuffleWide s b)
    (hbit : a.getLsbD 63 = b.getLsbD 63) : a = b := by
  have hh := congrArg split hS
  simp only [phShuffleWide, split_join] at hh
  have hl : laneShift (split a) 1 = laneShift (split b) 1 := by
    exact Prod.ext
      ((phShuffleLane_eq_iff_shift 64 s hs _ _).mp (congrArg Prod.fst hh))
      ((phShuffleLane_eq_iff_shift 64 s hs _ _).mp (congrArg Prod.snd hh))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h63 : i = 63
  · simpa only [h63] using hbit
  by_cases h127 : i = 127
  · simp only [h127, ha, hb]
  exact laneShift_split_kept_bit hl hi (by omega)
-- CHECKPOINT

theorem shuffled_wide_fibre_count {K : Type*} (f : K → Wide)
    (hf : Function.Injective f) (htop : ∀ k, (f k).getLsbD 127 = false)
    (s : ℕ) (hs : 0 < s) (z : Wide) (S : Finset K)
    (hS : ∀ k ∈ S, phShuffleWide s (f k) = z) : S.card ≤ 2 := by
  calc
    S.card ≤ (Finset.univ : Finset Bool).card := by
      apply Finset.card_le_card_of_injOn (fun k => (f k).getLsbD 63)
      · intro _ _
        exact Finset.mem_univ _
      · intro a ha b hb he
        exact hf (phShuffleWide_fibre_bit63 s hs _ _ (htop a) (htop b)
          ((hS a ha).trans (hS b hb).symm) he)
    _ = 2 := by decide
-- CHECKPOINT

theorem shuffled_wide_point_probability {K : Type*} [Fintype K] (f : K → Wide)
    (hf : Function.Injective f) (htop : ∀ k, (f k).getLsbD 127 = false)
    (s : ℕ) (hs : 0 < s) (z : Wide) :
    uniformProb (fun k => phShuffleWide s (f k) = z) ≤
      (2:ℚ≥0)/(Fintype.card K:ℚ≥0) := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  norm_cast
  apply shuffled_wide_fibre_count f hf htop s hs z
  intro k hk
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
-- CHECKPOINT

theorem phShuffleLane_low_bit (s : ℕ) (hs : 0 < s) (x : Word) :
    (phShuffleLane s x).getLsbD 0 = false := by
  unfold phShuffleLane
  split_ifs <;> simp [BitVec.getLsbD_shiftLeft, hs]
-- CHECKPOINT

/-- The two-fibre shuffler bound together with the two fixed low bits
gives the PROOF5 secondary slice constant 2*604^2. -/
theorem shuffled_projected_collision_bound {K : Type*} [Fintype K]
    (x y : K → Chunk) (f : K → Wide) (M : Chunk)
    (hf : Function.Injective f) (htop : ∀ k, (f k).getLsbD 127 = false)
    (s : ℕ) (hs : 0 < s)
    (hraw : ∀ k, xorChunk (x k) (y k) = xorChunk (split (phShuffleWide s (f k))) M) :
    uniformProb (fun k => project (x k) = project (y k)) ≤
      (729632:ℚ≥0)/(Fintype.card K:ℚ≥0) := by
  classical
  let T := (maskSet.filter (fun d => d%2 = (M.1.getLsbD 0).toNat)) ×ˢ
    (maskSet.filter (fun d => d%2 = (M.2.getLsbD 0).toNat))
  let label (k : K) :=
    (((x k).1.toNat ^^^ (y k).1.toNat, (x k).2.toNat ^^^ (y k).2.toNat),
      (f k).getLsbD 63)
  have hinj : Function.Injective label := by
    intro a b he
    have hp := congrArg Prod.fst he
    have hbit := congrArg Prod.snd he
    have hx : xorChunk (x a) (y a) = xorChunk (x b) (y b) := by
      apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
      · exact congrArg Prod.fst hp
      · exact congrArg Prod.snd hp
    rw [hraw a, hraw b] at hx
    have hc : split (phShuffleWide s (f a)) = split (phShuffleWide s (f b)) := by
      exact Prod.ext ((BitVec.xor_left_inj M.1).mp (congrArg Prod.fst hx))
        ((BitVec.xor_left_inj M.2).mp (congrArg Prod.snd hx))
    exact hf (phShuffleWide_fibre_bit63 s hs _ _ (htop a) (htop b)
      (split_injective hc) hbit)
  have hcover (k : K) (he : project (x k) = project (y k)) :
      label k ∈ T ×ˢ (Finset.univ : Finset Bool) := by
    have hm := Finset.mem_product.mp (project_eq_mask_cover (x k) (y k) he)
    have hmod : ((xorChunk (x k) (y k)).1.toNat%2 = (M.1.getLsbD 0).toNat) ∧
        ((xorChunk (x k) (y k)).2.toNat%2 = (M.2.getLsbD 0).toNat) := by
      rw [hraw k]
      simp only [phShuffleWide, split_join, xorChunk, word_low_bit_value,
        BitVec.getLsbD_xor, phShuffleLane_low_bit s hs, Bool.false_xor]
      trivial
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hm.1,hmod.1⟩,
        Finset.mem_filter.mpr ⟨hm.2,hmod.2⟩⟩, Finset.mem_univ _⟩
  have hc : (T ×ˢ (Finset.univ : Finset Bool)).card ≤ 729632 := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    apply (Nat.mul_le_mul_right 2 (show T.card ≤ 604*604 from ?_)).trans (by decide)
    exact (Finset.card_product _ _).le.trans
      (Nat.mul_le_mul (mask_low_bit_count _) (mask_low_bit_count _))
  exact (injective_target_probability label hinj _ _ hcover).trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity))
-- CHECKPOINT

end ProvenHashes.UMASH
