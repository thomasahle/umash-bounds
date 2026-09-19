import ProvenHashes.UMASHTwoPHCensus
import ProvenHashes.UMASHThreeCoordinates

/-! A finite weighted two-PH ledger. Conditional twisting estimates are
combined by min(a,b) ≤ sqrt(a)*sqrt(b), implemented using certified rational
square envelopes. The construction uses three compatibility bits. -/
namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet uniformProb wordFintype

def twoPHMaskPairs (h c : ℕ) : Finset (ℕ × ℕ) :=
  (maskSet ×ˢ maskSet).filter (fun uv => h < 3 ∨ (uv.2 ^^^ (2*uv.1))%8 = c)

theorem two_ph_mask_pair_weight_bounds (h c : ℕ) :
    (∑ t ∈ twoPHMaskPairs h c, twoPHRootLow t.2) ≤
      (if h < 3 then 852*47 else 7500 : ℚ≥0) ∧
    (∑ t ∈ twoPHMaskPairs h c, twoPHRootHigh t.2) ≤
      (if h < 3 then 852*38 else 5700 : ℚ≥0) := by
  by_cases hh : h < 3
  · simp only [twoPHMaskPairs, hh, true_or, Finset.filter_true, Finset.sum_product, ↓reduceIte]
    constructor
    · calc
        _ = (852:ℚ≥0)*(∑ e ∈ maskSet, twoPHRootLow e) := by
          simp only [Finset.sum_const, nsmul_eq_mul, maskSet_card, Nat.cast_ofNat]
        _ ≤ _ := mul_le_mul_of_nonneg_left two_ph_root_total_bounds.1 (zero_le _)
    · calc
        _ = (852:ℚ≥0)*(∑ e ∈ maskSet, twoPHRootHigh e) := by
          simp only [Finset.sum_const, nsmul_eq_mul, maskSet_card, Nat.cast_ofNat]
        _ ≤ _ := mul_le_mul_of_nonneg_left two_ph_root_total_bounds.2 (zero_le _)
  · simpa only [twoPHMaskPairs, hh, false_or, Finset.sum_filter, Finset.sum_product, ↓reduceIte]
      using two_ph_root_census_bounds c
-- CHECKPOINT

theorem two_ph_ledger_numeric (h c d : ℕ) (hh : h ≤ 15) :
    (2:ℚ≥0)^h * (∑ t ∈ twoPHMaskPairs h c, twoPHRootLow t.2) *
      (∑ t ∈ twoPHMaskPairs h d, twoPHRootHigh t.2) ≤ 1416246956032 := by
  have hL := (two_ph_mask_pair_weight_bounds h c).1
  have hH := (two_ph_mask_pair_weight_bounds h d).2
  by_cases h3 : h < 3
  · simp only [h3, ↓reduceIte] at hL hH
    calc
      _ ≤ (2:ℚ≥0)^2*(852*47)*(852*38) := by
        apply mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) hL
          (zero_le _) (zero_le _)) hH (zero_le _) (zero_le _)
      _ ≤ _ := by norm_num
  · simp only [h3, ↓reduceIte] at hL hH
    calc
      _ ≤ (2:ℚ≥0)^15*7500*5700 := by
        apply mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) hh) hL
          (zero_le _) (zero_le _)) hH (zero_le _) (zero_le _)
      _ ≤ _ := by norm_num
-- CHECKPOINT

/-- The entire four-lane mask union, with its conditional noise bound.
The uniform atom premise is discharged separately for literal PH slices. -/
theorem two_ph_weighted_partition {A B : Type*} [Fintype A] [Fintype B]
    (E : A × B → Prop) (U V : A → Chunk) (h c d : ℕ) (hh : h ≤ 15)
    (hcover : ∀ a b, E (a,b) →
      (U a).1.toNat ∈ maskSet ∧ (V a).1.toNat ∈ maskSet ∧
      (U a).2.toNat ∈ maskSet ∧ (V a).2.toNat ∈ maskSet)
    (hcompat : ∀ a, 3 ≤ h →
      ((V a).1.toNat ^^^ (2*(U a).1.toNat))%8 = c ∧
      ((V a).2.toNat ^^^ (2*(U a).2.toNat))%8 = d)
    (hatom : ∀ u v : Chunk, uniformProb (fun a => U a = u ∧ V a = v) ≤ (2:ℚ≥0)^h/q^2)
    (hnoise : ∀ a, uniformProb (fun b => E (a,b)) ≤
      min (twistLowWeight (V a).1.toNat) (twistHighWeight (V a).2.toNat)) :
    uniformProb E ≤ (1416246956032:ℚ≥0)/q^2 := by
  let T := twoPHMaskPairs h c ×ˢ twoPHMaskPairs h d
  let F (t : (ℕ × ℕ) × (ℕ × ℕ)) (a : A) :=
    (U a).1.toNat = t.1.1 ∧ (V a).1.toNat = t.1.2 ∧
    (U a).2.toNat = t.2.1 ∧ (V a).2.toNat = t.2.2
  let weight (t : (ℕ × ℕ) × (ℕ × ℕ)) := twoPHRootLow t.1.2*twoPHRootHigh t.2.2
  have hT (a : A) (b : B) (he : E (a,b)) : ∃ t ∈ T, F t a := by
    obtain ⟨hu,hv,hu',hv'⟩ := hcover a b he
    have hcomp : h < 3 ∨
        (((V a).1.toNat ^^^ (2*(U a).1.toNat))%8 = c ∧
        ((V a).2.toNat ^^^ (2*(U a).2.toNat))%8 = d) := by
      by_cases hs : h < 3
      · exact Or.inl hs
      · exact Or.inr (hcompat a (by omega))
    refine ⟨(((U a).1.toNat,(V a).1.toNat),((U a).2.toNat,(V a).2.toNat)), ?_,
      rfl,rfl,rfl,rfl⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu,hv⟩,
        hcomp.imp_right And.left⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu',hv'⟩,
        hcomp.imp_right And.right⟩
  have hcount (t) (_ht : t ∈ T) : uniformProb (F t) ≤ (2:ℚ≥0)^h/q^2 := by
    apply (probability_mono ?_).trans (hatom
      (BitVec.ofNat 64 t.1.1,BitVec.ofNat 64 t.2.1)
      (BitVec.ofNat 64 t.1.2,BitVec.ofNat 64 t.2.2))
    intro a ha
    change _ ∧ _ ∧ _ ∧ _ at ha
    constructor
    · apply Prod.ext
      · rw [← ha.1]; simp
      · rw [← ha.2.2.1]; simp
    · apply Prod.ext
      · rw [← ha.2.1]; simp
      · rw [← ha.2.2.2]; simp
  have hweight (t) (ht : t ∈ T) (a : A) (ha : F t a) :
      uniformProb (fun b => E (a,b)) ≤ weight t := by
    have hmem := Finset.mem_product.mp ht
    have hv := (Finset.mem_product.mp (Finset.mem_filter.mp hmem.1).1).2
    have hv' := (Finset.mem_product.mp (Finset.mem_filter.mp hmem.2).1).2
    have hn := hnoise a
    change _ ∧ _ ∧ _ ∧ _ at ha
    rw [ha.2.1,ha.2.2.2] at hn
    exact hn.trans (two_ph_twist_product_weight _ _ hv hv')
  calc
    _ ≤ ∑ t ∈ T, ((2:ℚ≥0)^h/q^2)*weight t :=
      probability_partition_prod_le E F T (fun _ => (2:ℚ≥0)^h/q^2) weight hT hweight hcount
    _ = ((2:ℚ≥0)^h*(∑ t ∈ twoPHMaskPairs h c, twoPHRootLow t.2)*
        (∑ t ∈ twoPHMaskPairs h d, twoPHRootHigh t.2))/q^2 := by
      simp only [T, weight, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (two_ph_ledger_numeric h c d hh) (zero_le _)
-- CHECKPOINT

end ProvenHashes.UMASH
