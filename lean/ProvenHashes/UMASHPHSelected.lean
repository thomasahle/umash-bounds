import ProvenHashes.UMASHDyadicNormalization
import ProvenHashes.UMASHJointHighPH

namespace ProvenHashes.UMASH
open Polynomial
open scoped BigOperators Classical
set_option maxHeartbeats 2000000
attribute [local irreducible] uniformProb wordFintype clmul

/-- The highest nonzero coefficient of a nonzero word lies in that word. -/
theorem bitPolynomial_leading {w : ℕ} (x : BitVec w) (hx : x ≠ 0) :
    (bitPolynomial x).natDegree < w ∧ x.getLsbD (bitPolynomial x).natDegree = true := by
  have hc : (bitPolynomial x).coeff (bitPolynomial x).natDegree =
      (bitPolynomial x).leadingCoeff := Polynomial.coeff_natDegree
  have hn := Polynomial.leadingCoeff_ne_zero.mpr (bitPolynomial_ne_zero hx)
  have hb : x.getLsbD (bitPolynomial x).natDegree = true := by
    rw [coeff_bitPolynomial] at hc
    cases hbit : x.getLsbD (bitPolynomial x).natDegree
    · exact False.elim (hn (hc.symm.trans (by simp [hbit, bitCoeff])))
    · rfl
  refine ⟨?_, hb⟩
  by_contra hge
  rw [BitVec.getLsbD_of_ge x _ (by omega)] at hb
  contradiction
-- CHECKPOINT

/-- Selected high-product bits below the multiplier degree eliminate the
corresponding high input bits by reverse triangular reconstruction. -/
theorem clmul_high_selected_count (d : Word) (hd : d ≠ 0)
    (S : Finset (Fin 64)) (hS : ∀ i ∈ S, i.val < (bitPolynomial d).natDegree)
    (pattern : Fin 64 → Bool) :
    (Finset.univ.filter (fun k : Word => ∀ i ∈ S,
      (split (clmul d k)).2.getLsbD i.val = pattern i)).card ≤ 2^(64-S.card) := by
  let j := (bitPolynomial d).natDegree
  have hj : j < 64 := (bitPolynomial_leading d hd).1
  let f (i : Fin 64) : Fin 64 := ⟨(64+i.val-j)%64, Nat.mod_lt _ (by decide)⟩
  let T := S.image f
  have hf (i : Fin 64) (hi : i ∈ S) : (f i).val = 64+i.val-j := by
    dsimp only [f]
    apply Nat.mod_eq_of_lt
    have h := hS i hi
    change i.val < j at h
    omega
  have hcard : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro i hi i' hi' he
    have hv := congrArg Fin.val he
    rw [hf i hi, hf i' hi'] at hv
    apply Fin.ext
    omega
  let bits (k : Word) : {t : Fin 64 // t ∉ T} → Bool := fun t => k.getLsbD t.val.val
  calc
    _ ≤ (Finset.univ : Finset ({t : Fin 64 // t ∉ T} → Bool)).card := by
      apply Finset.card_le_card_of_injOn bits
      · intro k _; exact Finset.mem_univ _
      · intro x hx y hy hbits
        by_contra hxy
        have hw : x ^^^ y ≠ 0 := fun h => hxy (BitVec.xor_eq_zero_iff.mp h)
        let t := (bitPolynomial (x ^^^ y)).natDegree
        have ht : t < 64 := (bitPolynomial_leading (x ^^^ y) hw).1
        have htb := (bitPolynomial_leading (x ^^^ y) hw).2
        have htT : (⟨t,ht⟩ : Fin 64) ∈ T := by
          by_contra hn
          have he := congrFun hbits ⟨⟨t,ht⟩,hn⟩
          change x.getLsbD t = y.getLsbD t at he
          have hz : (x ^^^ y).getLsbD t = false := by
            simp only [BitVec.getLsbD_xor, he, Bool.xor_self]
          rw [hz] at htb
          contradiction
        obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp htT
        have hti := congrArg Fin.val hit
        rw [hf i hi] at hti
        have hidx : j+t = i.val+64 := by dsimp only at hti; omega
        have he := ((Finset.mem_filter.mp hx).2 i hi).trans ((Finset.mem_filter.mp hy).2 i hi).symm
        have he' : (clmul d x).getLsbD (j+t) = (clmul d y).getLsbD (j+t) := by
          simpa only [split, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
            i.isLt, decide_true, Bool.true_and, hidx, Nat.add_comm] using he
        have hz : (bitPolynomial (clmul d (x ^^^ y))).coeff (j+t) = 0 := by
          rw [coeff_bitPolynomial, clmul_xor_right, BitVec.getLsbD_xor, he', Bool.xor_self]
          rfl
        have hn : (bitPolynomial (clmul d (x ^^^ y))).coeff (j+t) ≠ 0 := by
          rw [bitPolynomial_clmul]
          change (bitPolynomial d*bitPolynomial (x ^^^ y)).coeff
            ((bitPolynomial d).natDegree+(bitPolynomial (x ^^^ y)).natDegree) ≠ 0
          rw [Polynomial.coeff_mul_degree_add_degree]
          exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (bitPolynomial_ne_zero hd))
            (Polynomial.leadingCoeff_ne_zero.mpr (bitPolynomial_ne_zero hw))
        exact hn hz
    _ = 2^(64-S.card) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hcard]
-- CHECKPOINT

/-- Selected low-product bits at or above the multiplier valuation eliminate
the corresponding low input bits by forward triangular reconstruction. -/
theorem clmul_low_selected_count (d : Word) (hd : d ≠ 0)
    (S : Finset (Fin 64)) (hS : ∀ i ∈ S, (bitPolynomial d).natTrailingDegree ≤ i.val)
    (pattern : Fin 64 → Bool) :
    (Finset.univ.filter (fun k : Word => ∀ i ∈ S,
      (split (clmul d k)).1.getLsbD i.val = pattern i)).card ≤ 2^(64-S.card) := by
  let j := (bitPolynomial d).natTrailingDegree
  have hj : j < 64 := (bitPolynomial_trailing d hd).1
  let f (i : Fin 64) : Fin 64 := ⟨i.val-j, by omega⟩
  let T := S.image f
  have hcard : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro i hi i' hi' he
    have hv := congrArg Fin.val he
    have hi := hS i hi
    have hi' := hS i' hi'
    apply Fin.ext
    dsimp only [f,j] at hv
    omega
  let bits (k : Word) : {t : Fin 64 // t ∉ T} → Bool := fun t => k.getLsbD t.val.val
  calc
    _ ≤ (Finset.univ : Finset ({t : Fin 64 // t ∉ T} → Bool)).card := by
      apply Finset.card_le_card_of_injOn bits
      · intro k _; exact Finset.mem_univ _
      · intro x hx y hy hbits
        by_contra hxy
        have hw : x ^^^ y ≠ 0 := fun h => hxy (BitVec.xor_eq_zero_iff.mp h)
        let t := (bitPolynomial (x ^^^ y)).natTrailingDegree
        have ht : t < 64 := (bitPolynomial_trailing (x ^^^ y) hw).1
        have htb := (bitPolynomial_trailing (x ^^^ y) hw).2
        have htT : (⟨t,ht⟩ : Fin 64) ∈ T := by
          by_contra hn
          have he := congrFun hbits ⟨⟨t,ht⟩,hn⟩
          change x.getLsbD t = y.getLsbD t at he
          have hz : (x ^^^ y).getLsbD t = false := by
            simp only [BitVec.getLsbD_xor, he, Bool.xor_self]
          rw [hz] at htb
          contradiction
        obtain ⟨i, hi, hit⟩ := Finset.mem_image.mp htT
        have hti := congrArg Fin.val hit
        have hi' := hS i hi
        have hidx : j+t = i.val := by dsimp only [f,j] at hti ⊢; omega
        have he := ((Finset.mem_filter.mp hx).2 i hi).trans ((Finset.mem_filter.mp hy).2 i hi).symm
        have he' : (clmul d x).getLsbD (j+t) = (clmul d y).getLsbD (j+t) := by
          simpa only [split, BitVec.getLsbD_setWidth,
            i.isLt, decide_true, Bool.true_and, hidx] using he
        have hz : (bitPolynomial (clmul d (x ^^^ y))).coeff (j+t) = 0 := by
          rw [coeff_bitPolynomial, clmul_xor_right, BitVec.getLsbD_xor, he', Bool.xor_self]
          rfl
        have hn : (bitPolynomial (clmul d (x ^^^ y))).coeff (j+t) ≠ 0 := by
          rw [bitPolynomial_clmul]
          change (bitPolynomial d*bitPolynomial (x ^^^ y)).coeff
            ((bitPolynomial d).natTrailingDegree+(bitPolynomial (x ^^^ y)).natTrailingDegree) ≠ 0
          rw [Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]
          exact mul_ne_zero (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hd))
            (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (bitPolynomial_ne_zero hw))
        exact hn hz
    _ = 2^(64-S.card) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hcard]
-- CHECKPOINT

/-- An upper interval of mask positions is the divided mask at smaller width. -/
theorem mask_bit_set_above_card (n j e : ℕ) (hj : j ≤ n) :
    ((maskBitSet n e).filter (fun i => j ≤ i.val)).card =
      (maskBitSet (n-j) (e/2^j)).card := by
  apply Finset.card_bij (fun i hi => (⟨i.val-j, by
    have hij := (Finset.mem_filter.mp hi).2
    omega⟩ : Fin (n-j)))
  · intro i hi
    have hij := (Finset.mem_filter.mp hi).2
    have hib := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    simp only [maskBitSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.testBit_div_two_pow, Nat.sub_add_cancel hij, hib]
  · intro i hi i' hi' he
    have hij := (Finset.mem_filter.mp hi).2
    have hij' := (Finset.mem_filter.mp hi').2
    have hv := congrArg Fin.val he
    apply Fin.ext
    dsimp only at hv
    omega
  · intro i hi
    have hib := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val+j, by omega⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · simpa only [maskBitSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Nat.testBit_div_two_pow] using hib
      · dsimp only; omega
    · apply Fin.ext
      exact Nat.add_sub_cancel _ _
-- CHECKPOINT

/-- A lower interval of mask positions is the same mask at smaller width. -/
theorem mask_bit_set_below_card (n j e : ℕ) (hj : j ≤ n) :
    ((maskBitSet n e).filter (fun i => i.val < j)).card = (maskBitSet j e).card := by
  apply Finset.card_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin j))
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2⟩
  · intro i _ i' _ he
    exact Fin.ext (congrArg (fun u : Fin j => u.val) he)
  · intro i hi
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hj⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, i.isLt⟩
-- CHECKPOINT

/-- A mask equality fixes each selected bit even after an arbitrary XOR offset. -/
theorem xor_mask_selected_bit (x offset : Word) (e z i : ℕ)
    (he : (offset ^^^ x).toNat &&& e = z) (hi : e.testBit i = true) :
    x.getLsbD i = (offset.getLsbD i ^^ z.testBit i) := by
  have hh := congrArg (fun v : ℕ => v.testBit i) he
  simp only [Nat.testBit_and, hi, Bool.and_true] at hh
  change (offset ^^^ x).getLsbD i = z.testBit i at hh
  rw [BitVec.getLsbD_xor] at hh
  have hh' := congrArg (fun b : Bool => offset.getLsbD i ^^ b) hh
  simpa only [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor] using hh'
-- CHECKPOINT

/-- Cardinality form of a fixed number of independent word bits. -/
theorem word_probability_of_bit_count (E : Word → Prop) (h : ℕ) (hh : h ≤ 64)
    (hc : (Finset.univ.filter E).card ≤ 2^(64-h)) :
    uniformProb E ≤ (1:ℚ≥0)/2^h := by
  have hp : (2:ℚ≥0)^64 = 2^(64-h)*2^h := by rw [← pow_add, Nat.sub_add_cancel hh]
  unfold uniformProb
  rw [word_card]
  calc
    _ ≤ (2:ℚ≥0)^(64-h)/(2:ℚ≥0)^64 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := by rw [hp]; field_simp
-- CHECKPOINT

/-- The high checksum pattern bound for a fixed nonzero first operand.
Only selected positions below its degree contribute independent bits. -/
theorem clmul_high_mask_probability (d : Word) (hd : d ≠ 0) (offset : Word) (e z : ℕ) :
    uniformProb (fun k : Word => (offset ^^^ (split (clmul d k)).2).toNat &&& e = z) ≤
      (1:ℚ≥0)/2^(maskBitSet (bitPolynomial d).natDegree e).card := by
  let j := (bitPolynomial d).natDegree
  let S := (maskBitSet 64 e).filter (fun i => i.val < j)
  have hj : j < 64 := (bitPolynomial_leading d hd).1
  have hS : S.card = (maskBitSet j e).card := mask_bit_set_below_card 64 j e hj.le
  rw [← hS]
  apply (probability_mono (F := fun k : Word => ∀ i ∈ S,
    (split (clmul d k)).2.getLsbD i.val = (offset.getLsbD i.val ^^ z.testBit i.val)) ?_).trans
  · apply word_probability_of_bit_count _ S.card
      ((Finset.card_le_univ S).trans_eq (Fintype.card_fin 64))
    convert clmul_high_selected_count d hd S (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i => offset.getLsbD i.val ^^ z.testBit i.val) using 1
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro k hk i hi
    exact xor_mask_selected_bit _ offset e z i.val hk
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
-- CHECKPOINT

/-- The low checksum pattern bound for a fixed nonzero first operand.
Only selected positions at or above its valuation contribute independent bits. -/
theorem clmul_low_mask_probability (d : Word) (hd : d ≠ 0) (offset : Word) (e z : ℕ) :
    uniformProb (fun k : Word => (offset ^^^ (split (clmul d k)).1).toNat &&& e = z) ≤
      (1:ℚ≥0)/2^(maskBitSet (64-(bitPolynomial d).natTrailingDegree)
        (e/2^(bitPolynomial d).natTrailingDegree)).card := by
  let j := (bitPolynomial d).natTrailingDegree
  let S := (maskBitSet 64 e).filter (fun i => j ≤ i.val)
  have hj : j < 64 := (bitPolynomial_trailing d hd).1
  have hS : S.card = (maskBitSet (64-j) (e/2^j)).card := mask_bit_set_above_card 64 j e hj.le
  rw [← hS]
  apply (probability_mono (F := fun k : Word => ∀ i ∈ S,
    (split (clmul d k)).1.getLsbD i.val = (offset.getLsbD i.val ^^ z.testBit i.val)) ?_).trans
  · apply word_probability_of_bit_count _ S.card
      ((Finset.card_le_univ S).trans_eq (Fintype.card_fin 64))
    convert clmul_low_selected_count d hd S (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i => offset.getLsbD i.val ^^ z.testBit i.val) using 1
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro k hk i hi
    exact xor_mask_selected_bit _ offset e z i.val hk
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
-- CHECKPOINT

end ProvenHashes.UMASH
