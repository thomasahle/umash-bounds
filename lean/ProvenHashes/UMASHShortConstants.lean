import ProvenHashes.UMASHShortFingerprint
import ProvenHashes.UMASHShortLongIdentity
import ProvenHashes.UMASHModePolynomial

namespace ProvenHashes.UMASH
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype

theorem unfinalize_bijective : Function.Bijective unfinalize := by
  have hi : Function.Injective unfinalize := by
    intro a b h
    simpa only [finalize_unfinalize] using congrArg finalize h
  exact ⟨hi,Finite.surjective_of_injective hi⟩
-- CHECKPOINT

theorem bijective_word_field_probability (f : Word → Word) (hf : Function.Bijective f) (t : Field) :
    uniformProb (fun v : Word => ((f v).toNat : Field) = t) ≤ (9:ℚ≥0)/q := by
  let T := Finset.univ.filter (fun w : Word => (w.toNat : Field) = t)
  calc
    _ ≤ uniformProb (fun v : Word => ∃ w ∈ T, f v = w) := by
      apply probability_mono
      intro v hv
      exact ⟨f v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
    _ ≤ ∑ w ∈ T, uniformProb (fun v => f v = w) := probability_union_bound _ _
    _ = T.card/(q:ℚ≥0) := by
      simp only [probability_bijective_point f hf,word_card,Finset.sum_const,nsmul_eq_mul,mul_one_div]
    _ ≤ _ := div_le_div_of_nonneg_right (Nat.cast_le.mpr (field_word_fibre t)) (by positivity)
-- CHECKPOINT

theorem short_constant_mode_slice (mode : Bool) (seed : Word) (m : Message)
    (hm : m.length ≤ 8) (k : OHKey) :
    uniformProb (fun v : Word => ((unfinalize (shortHash
      (Function.update k ⟨m.length+(if mode then 4 else 0),by cases mode <;> simp_all <;> omega⟩ v)
      seed m mode)).toNat : Field) = 0) ≤ (9:ℚ≥0)/q := by
  apply bijective_word_field_probability
  apply unfinalize_bijective.comp
  cases mode
  · exact shortHash_noise_bijective seed m (by omega) k
  · exact shortHash_secondary_noise_bijective seed m (by omega) k
-- CHECKPOINT

theorem short_constant_mode_probability (mode : Bool) (seed : Word) (m : Message)
    (hm : m.length ≤ 8) :
    uniformProb (fun k : OHKey => ((unfinalize (shortHash k seed m mode)).toNat : Field) = 0) ≤
      (9:ℚ≥0)/q := by
  exact probability_le_of_update _
    (⟨m.length+(if mode then 4 else 0),by cases mode <;> simp_all <;> omega⟩ : Fin 34) _
    (fun k => short_constant_mode_slice mode seed m hm k)
-- CHECKPOINT

theorem short_constants_joint_probability (seed : Word) (m : Message) (hm : m.length ≤ 8) :
    uniformProb (fun k : OHKey =>
      ((unfinalize (shortHash k seed m false)).toNat : Field) = 0 ∧
      ((unfinalize (shortHash k seed m true)).toNat : Field) = 0) ≤ (81:ℚ≥0)/q^2 := by
  let P := fun k : OHKey => ((unfinalize (shortHash k seed m false)).toNat : Field) = 0
  let Q := fun k : OHKey => ((unfinalize (shortHash k seed m true)).toNat : Field) = 0
  let i : Fin 34 := ⟨m.length+4,by omega⟩
  have hfix (k : OHKey) (v : Word) : P (Function.update k i v) ↔ P k := by
    simp only [P,shortHash_eq_mixer,keyWord_update k i v m.length (by omega),i,
      show m.length ≠ m.length+4 by omega,↓reduceIte]
  have h := probability_and_update_le P Q i ((9:ℚ≥0)/q) hfix
    (fun k => short_constant_mode_slice true seed m hm k)
  exact (h.trans (mul_le_mul_of_nonneg_right (short_constant_mode_probability false seed m hm)
    (by positivity))).trans_eq (by ring)
-- CHECKPOINT

theorem mode_short_long_constant_zero (mode : Bool) (k : OHKey) (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : 8 < y.length)
    (he : modePolynomial mode k seed x = modePolynomial mode k seed y) :
    ((unfinalize (shortHash k seed x mode)).toNat : Field) = 0 := by
  have hh := congrArg (fun P : Polynomial Field => P.coeff 0) he
  simpa only [modePolynomial,if_pos hx,if_neg (by omega : ¬y.length ≤ 8),
    Polynomial.coeff_C_zero,blockPolynomial_constant] using hh
-- CHECKPOINT

theorem mode_short_long_identity_probability (mode : Bool) (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : 8 < y.length) :
    uniformProb (fun k : OHKey => modePolynomial mode k seed x = modePolynomial mode k seed y) ≤
      (9:ℚ≥0)/q :=
  (probability_mono (fun k hk => mode_short_long_constant_zero mode k seed x y hx hy hk)).trans
    (short_constant_mode_probability mode seed x hx)
-- CHECKPOINT

theorem short_long_joint_identity_probability (seed : Word) (x y : Message)
    (hx : x.length ≤ 8) (hy : 8 < y.length) :
    uniformProb (fun k : OHKey =>
      modePolynomial false k seed x = modePolynomial false k seed y ∧
      modePolynomial true k seed x = modePolynomial true k seed y) ≤ (81:ℚ≥0)/q^2 :=
  (probability_mono (fun k hk => And.intro
    (mode_short_long_constant_zero false k seed x y hx hy hk.1)
    (mode_short_long_constant_zero true k seed x y hx hy hk.2))).trans
      (short_constants_joint_probability seed x hx)
-- CHECKPOINT

end ProvenHashes.UMASH
