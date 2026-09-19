import ProvenHashes.UMASHMaskCensus3125
import ProvenHashes.UMASHGroupedFibre
import ProvenHashes.UMASHAdditiveProductTarget

namespace ProvenHashes.UMASH
open scoped Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] maskSet maskPatterns uniformProb wordFintype Finset.range Finset.filter Finset.product

theorem liftingLabel_zero_iff (r m t : ℕ) (hr : 4 ≤ r) (ht : t ∈ maskPatterns m) :
    liftingLabel r m t = toLex (0,0) ↔ m = 0 ∧ t = 0 := by
  constructor
  · intro h
    have hc := congrArg (fun z : ℕ ×ₗ ℤ => z.2) h
    exact maskPattern_zero_class r m t hr ht hc
  · rintro ⟨rfl,rfl⟩
    simp [liftingLabel]
-- CHECKPOINT

theorem zero_mem_liftingClasses (r : ℕ) : toLex (0,0) ∈ liftingClasses r := by
  apply Finset.mem_image.mpr
  refine ⟨⟨0,0⟩, ?_, ?_⟩
  · apply Finset.mem_sigma.mpr
    constructor
    · simpa using congruent_xor_mem_maskSet 0 0 (by norm_num [q]) (by norm_num [q]) rfl
    · simpa using congruent_pattern 0 0 (by norm_num [q]) (by norm_num [q]) rfl
  · simp [liftingLabel]
-- CHECKPOINT

def enhHighMask (δ ε tag tag' M : ℕ) (ab : Word × Word) : ℕ :=
  enhHighNat q ab.1.toNat ab.2.toNat tag M ^^^
    enhHighNat q ((ab.1.toNat+δ)%q) ((ab.2.toNat+ε)%q) tag' M

/-- The zero class costs q operand pairs across both wrap branches together. -/
theorem enh_zero_class_count (δ ε tag tag' M : ℕ)
    (hδq : δ < q) (hδ0 : δ ≠ 0) (hεq : ε < q) :
    (Finset.univ.filter (fun ab => enhLowEqualEvent δ ε tag tag' M ab ∧
      enhHighMask δ ε tag tag' M ab = 0)).card ≤ q := by
  apply le_trans _ (additive_product_target_count δ ε (-(q:ℤ)*((tag':ℤ)-tag)) hδq hδ0 hεq)
  apply Finset.card_le_card
  intro ab hab
  have he := (Finset.mem_filter.mp hab).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    enh_zero_mask_product_target q ab.1.toNat ab.2.toNat
      ((ab.1.toNat+δ)%q) ((ab.2.toNat+ε)%q) tag tag' M he.1.1 he.2⟩
-- CHECKPOINT

def enhNonzeroClassEvent (δ ε tag tag' M : ℕ) (ab : Word × Word) : Prop :=
  enhLowEqualEvent δ ε tag tag' M ab ∧ enhHighMask δ ε tag tag' M ab ≠ 0
attribute [local irreducible] enhNonzeroClassEvent

/-- Nonzero classes cost at most two candidates for each first operand. -/
theorem enh_nonzero_class_count (r δ ε tag tag' M : ℕ)
    (h4 : 4 ≤ r) (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hεq : ε < q) (hM : M < q) :
    (Finset.univ.filter (enhNonzeroClassEvent δ ε tag tag' M)).card ≤ q*(2*((liftingClasses r).card-1)) := by
  classical
  let X (ab : Word × Word) := enhHighNat q ab.1.toNat ab.2.toNat tag M
  let Y (ab : Word × Word) := enhHighNat q ((ab.1.toNat+δ)%q) ((ab.2.toNat+ε)%q) tag' M
  let lab (ab : Word × Word) := liftingLabel r (X ab ^^^ Y ab) (X ab &&& (X ab ^^^ Y ab))
  let f (ab : Word × Word) : ℕ × (ℕ × (ℕ ×ₗ ℤ)) := (ab.1.toNat, ((ab.2.toNat+ε)/q, lab ab))
  have hX (ab : Word × Word) : X ab < q := enhHighNat_lt 64 _ _ _ _ hM
  have hY (ab : Word × Word) : Y ab < q := enhHighNat_lt 64 _ _ _ _ hM
  calc
    _ ≤ ((Finset.range q) ×ˢ ((Finset.range 2) ×ˢ (liftingClasses r).erase (toLex (0,0)))).card := by
      apply event_card_le_targets _ f
      · intro ab he
        unfold enhNonzeroClassEvent at he
        refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ab.1.isLt,
          Finset.mem_product.mpr ⟨?_, ?_⟩⟩
        · apply Finset.mem_range.mpr
          apply (Nat.div_lt_iff_lt_mul (by norm_num [q] : 0 < q)).mpr
          have hbq : ab.2.toNat < q := ab.2.isLt
          omega
        · have hp := congruent_pattern _ _ (hX ab) (hY ab) he.1.2
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · intro hz
            exact he.2 (((liftingLabel_zero_iff r (X ab ^^^ Y ab)
              (X ab &&& (X ab ^^^ Y ab)) h4 hp).mp hz).1)
          · apply Finset.mem_image.mpr
            refine ⟨⟨X ab ^^^ Y ab, X ab &&& (X ab ^^^ Y ab)⟩, ?_, rfl⟩
            exact Finset.mem_sigma.mpr ⟨congruent_xor_mem_maskSet _ _ (hX ab) (hY ab) he.1.2, hp⟩
      · intro a b ha hb hab
        unfold enhNonzeroClassEvent at ha hb
        have hA : a.1 = b.1 := BitVec.eq_of_toNat_eq (congrArg Prod.fst hab)
        rcases a with ⟨A,B₁⟩
        rcases b with ⟨A',B₂⟩
        dsimp only at hA
        subst A'
        refine Prod.ext rfl (BitVec.eq_of_toNat_eq ?_)
        have hw := congrArg (fun v : ℕ × (ℕ × (ℕ ×ₗ ℤ)) => v.2.1) hab
        have hlab := congrArg (fun v : ℕ × (ℕ × (ℕ ×ₗ ℤ)) => v.2.2) hab
        have hm := congrArg (fun z : ℕ ×ₗ ℤ => z.1) hlab
        have hc := congrArg (fun z : ℕ ×ₗ ℤ => z.2) hlab
        apply enh_wrap_class_fibre_unique 64 r A.toNat δ ε B₁.toNat B₂.toNat tag tag' M
          (X (A,B₁) ^^^ Y (A,B₁)) (X (A,B₁) &&& (X (A,B₁) ^^^ Y (A,B₁)))
          (X (A,B₂) ^^^ Y (A,B₂)) (X (A,B₂) &&& (X (A,B₂) ^^^ Y (A,B₂)))
          (by omega) hr hδ hε hodd B₁.isLt B₂.isLt (Nat.xor_lt_two_pow (hX _) (hY _))
          (by simp only [Nat.and_assoc, Nat.and_self])
          (by simp only [Nat.and_assoc, Nat.and_self]) hm hc hw ha.1.1 hb.1.1 rfl rfl rfl rfl
    _ = q*(2*((liftingClasses r).card-1)) := by
      rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
        Finset.card_erase_of_mem (zero_mem_liftingClasses r)]
-- CHECKPOINT

/-- PROOF3's grouped ENH count, before the finite maximum is substituted. -/
theorem enh_grouped_class_count (r δ ε tag tag' M : ℕ)
    (h4 : 4 ≤ r) (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hδq : δ < q) (hεq : ε < q) (hM : M < q) :
    (Finset.univ.filter (enhLowEqualEvent δ ε tag tag' M)).card ≤
      q*(2*(liftingClasses r).card-1) := by
  classical
  have hδ0 : δ ≠ 0 := by intro hz; simp [hz] at hodd
  have hzero := enh_zero_class_count δ ε tag tag' M hδq hδ0 hεq
  have hnonzero := enh_nonzero_class_count r δ ε tag tag' M h4 hr hδ hε hodd hεq hM
  unfold enhNonzeroClassEvent at hnonzero
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.univ.filter (enhLowEqualEvent δ ε tag tag' M))
    (fun ab => enhHighMask δ ε tag tag' M ab = 0)
  simp only [Finset.filter_filter] at hsplit
  have hf : 1 ≤ (liftingClasses r).card := Finset.one_le_card.mpr ⟨_, zero_mem_liftingClasses r⟩
  have hformula : q + q*(2*((liftingClasses r).card-1)) = q*(2*(liftingClasses r).card-1) := by
    have hi : 2*((liftingClasses r).card-1)+1 = 2*(liftingClasses r).card-1 := by omega
    rw [← hi, Nat.mul_add, Nat.mul_one, Nat.add_comm]
  calc
    _ = _ := hsplit.symm
    _ ≤ q + q*(2*((liftingClasses r).card-1)) := Nat.add_le_add hzero (by convert hnonzero using 2 <;> ext ab <;> simp)
    _ = _ := hformula
-- CHECKPOINT

theorem enh_grouped_class_probability (r δ ε tag tag' M : ℕ)
    (h4 : 4 ≤ r) (hr : r < 64) (hδ : 2^r ∣ δ) (hε : 2^r ∣ ε)
    (hodd : (δ/2^r)%2 = 1) (hδq : δ < q) (hεq : ε < q) (hM : M < q) :
    uniformProb (enhLowEqualEvent δ ε tag tag' M) ≤
      ((2*(liftingClasses r).card-1 : ℕ):ℚ≥0)/q := by
  classical
  have hc := enh_grouped_class_count r δ ε tag tag' M h4 hr hδ hε hodd hδq hεq hM
  have hw : Fintype.card Word = q :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin q)
  unfold uniformProb
  calc
    _ ≤ ((q*(2*(liftingClasses r).card-1) : ℕ):ℚ≥0)/(Fintype.card (Word × Word):ℚ≥0) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by rw [Fintype.card_prod, hw, Nat.cast_mul, Nat.cast_mul]; field_simp
-- CHECKPOINT

end ProvenHashes.UMASH
