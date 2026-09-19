import ProvenHashes.UMASHCorrectedObligations

namespace ProvenHashes.UMASH
open scoped Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype Finset.filter Finset.product

theorem xorChunk_fixed_injective (M : Chunk) : Function.Injective (xorChunk M) := by
  intro x y h
  exact Prod.ext ((BitVec.xor_right_inj M.1).mp (congrArg Prod.fst h))
    ((BitVec.xor_right_inj M.2).mp (congrArg Prod.snd h))
-- CHECKPOINT

theorem tagFold_injective (tag : Word) : Function.Injective (tagFold tag) :=
  Function.LeftInverse.injective (untagFold_tagFold tag)
-- CHECKPOINT

/-- With a nonzero first operand, the tagged and folded product determines the
second operand as an ordinary integer, even after an arbitrary common XOR. -/
theorem masked_enh_second_injective (tag : Word) (M : Chunk) (A : Word) (hA : A ≠ 0) :
    Function.Injective (fun B : Word => xorChunk M (enh (A,B) (0,0) tag)) := by
  intro B C h
  have he := xorChunk_fixed_injective M h
  simp only [enh_eq_tagFold, zero_add] at he
  have hw := tagFold_injective tag he
  have hp := congrArg BitVec.toNat hw
  simp only [widened_product_toNat] at hp
  have hAz : A.toNat ≠ 0 := by
    intro ha
    apply hA
    apply BitVec.eq_of_toNat_eq
    simpa only [BitVec.toNat_zero] using ha
  exact BitVec.eq_of_toNat_eq (mul_left_cancel₀ hAz hp)
-- CHECKPOINT

/-- The zero first-operand slice contributes at most q keys. All other keys
inject into 81 possible projected raw values times q-1 first operands. -/
theorem exceptional_slice_count {A B C : Type*} [Fintype A] [Fintype B]
    (a₀ : A) (E : A × B → Prop) (f : A × B → C) (T : Finset C)
    (hcover : ∀ ab, E ab → f ab ∈ T)
    (hinj : ∀ a, a ≠ a₀ → Function.Injective (fun b => f (a,b))) :
    (Finset.univ.filter E).card ≤ Fintype.card B + T.card*(Fintype.card A-1) := by
  classical
  let S := Finset.univ.filter E
  have h0 : (S.filter (fun k => k.1 = a₀)).card ≤ Fintype.card B := by
    calc
      _ ≤ (Finset.univ : Finset B).card := by
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro k _; exact Finset.mem_univ _
        · intro a ha b hb hab
          exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
      _ = _ := Finset.card_univ
  have h1 : (S.filter (fun k => ¬k.1 = a₀)).card ≤ T.card*(Fintype.card A-1) := by
    calc
      _ ≤ (T ×ˢ (Finset.univ.erase a₀)).card := by
        apply Finset.card_le_card_of_injOn (fun k : A × B => (f k, k.1))
        · intro k hk
          exact Finset.mem_product.mpr
            ⟨hcover k (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2,
              Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hk).2, Finset.mem_univ _⟩⟩
        · intro a ha b hb hab
          have hf : a.1 = b.1 := congrArg Prod.snd hab
          refine Prod.ext hf ?_
          apply hinj a.1 (Finset.mem_filter.mp ha).2
          have hp := congrArg Prod.fst hab
          change f (a.1,a.2) = f (b.1,b.2) at hp
          rwa [← hf] at hp
      _ = _ := by
        rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ]
  have hs := Finset.filter_card_add_filter_neg_card_eq_card (s := S)
    (fun k : A × B => k.1 = a₀)
  change S.card ≤ _
  omega
-- CHECKPOINT

def enhPointEvent (tag : Word) (M : Chunk) (z : Field × Field) (k : Chunk) : Prop :=
  project (xorChunk M (enh k (0,0) tag)) = z

theorem enh_projected_point_count (tag : Word) (M : Chunk) (z : Field × Field) :
    (Finset.univ.filter (enhPointEvent tag M z)).card ≤ 82*q-81 := by
  classical
  have h := exceptional_slice_count (0 : Word) (enhPointEvent tag M z)
    (fun k : Chunk => xorChunk M (enh k (0,0) tag))
    (Finset.univ.filter (fun c : Chunk => project c = z))
    (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    (masked_enh_second_injective tag M)
  rw [word_card] at h
  have hp := Nat.mul_le_mul_right (q-1) (project_fibre z)
  have hq : 1 ≤ q := by norm_num [q]
  omega
-- CHECKPOINT

theorem enh_projected_point_mass : ENHProjectedPointMass := by
  intro tag M z
  have hc := enh_projected_point_count tag M z
  change uniformProb (enhPointEvent tag M z) ≤ _
  unfold uniformProb
  rw [Fintype.card_prod, word_card]
  simpa only [Nat.cast_mul, pow_two] using
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) (by positivity :
      (0 : ℚ≥0) ≤ (q*q : ℕ))
-- CHECKPOINT

theorem enh_projected_point_mass_data (tag : Word) (M data : Chunk) (z : Field × Field) :
    uniformProb (fun k : Chunk => project (xorChunk M (enh k data tag)) = z) ≤
      ((82*q-81 : ℕ) : ℚ≥0)/(q:ℚ≥0)^2 := by
  let e : Chunk ≃ Chunk := Equiv.prodCongr (Equiv.addLeft data.1) (Equiv.addLeft data.2)
  have he (k : Chunk) : enh (e k) (0,0) tag = enh k data tag := by
    change enh (data.1+k.1, data.2+k.2) (0,0) tag = enh k data tag
    simp only [enh, zero_add]
  calc
    _ = uniformProb (fun k : Chunk => project (xorChunk M (enh (e k) (0,0) tag)) = z) := by
      exact congrArg uniformProb (funext (fun k =>
        congrArg (fun c : Chunk => project (xorChunk M c) = z) (he k).symm))
    _ = uniformProb (enhPointEvent tag M z) :=
      uniformProb_equiv e (enhPointEvent tag M z)
    _ ≤ _ := enh_projected_point_mass tag M z
-- CHECKPOINT

theorem enh_projected_point_mass_lt (tag : Word) (M data : Chunk) (z : Field × Field) :
    uniformProb (fun k : Chunk => project (xorChunk M (enh k data tag)) = z) <
      (82:ℚ≥0)/q := by
  exact (enh_projected_point_mass_data tag M data z).trans_lt (by norm_num [q])
-- CHECKPOINT

end ProvenHashes.UMASH
